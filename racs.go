package main

import (
	"bytes"
	"crypto/aes"
	"crypto/cipher"
	"crypto/rand"
	"crypto/sha256"
	"database/sql"
	"encoding/hex"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"io/ioutil"
	"net/http"
	"net/url"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"text/template"
	"time"

	_ "github.com/mattn/go-sqlite3"
	"github.com/msteinert/pam"
	"github.com/withmandala/go-log"
)

var logger = log.New(os.Stderr)

type state int

const (
	DELETING        state = -3
	DELETE_ERROR    state = -2
	DELETE_SUCCESS  state = -1
	NONE            state = 0
	CREATING        state = 1
	CREATE_ERROR    state = 2
	CREATE_SUCCESS  state = 3
	CLEANING        state = 4
	CLEAN_ERROR     state = 5
	CLEAN_SUCCESS   state = 6
	CLONING         state = 7
	CLONE_ERROR     state = 8
	CLONE_SUCCESS   state = 9
	PREPARING       state = 10
	PREPARE_ERROR   state = 11
	PREPARE_SUCCESS state = 12
	PULLING         state = 13
	PULL_ERROR      state = 14
	PULL_SUCCESS    state = 15
	BUILDING        state = 16
	BUILD_ERROR     state = 17
	BUILD_SUCCESS   state = 18
	PACKAGING       state = 19
	PACKAGE_ERROR   state = 20
	PACKAGE_SUCCESS state = 21
	PUSHING         state = 22
	PUSH_ERROR      state = 23
	PUSH_SUCCESS    state = 24
)

func (s state) String() string {
	return [28]string{
		"DELETING", "DELETE_ERROR", "DELETE_SUCCESS",
		"NONE",
		"CREATING", "CREATE_ERROR", "CREATE_SUCCESS",
		"CLEANING", "CLEAN_ERROR", "CLEAN_SUCCESS",
		"CLONING", "CLONE_ERROR", "CLONE_SUCCESS",
		"PREPARING", "PREPARE_ERROR", "PREPARE_SUCCESS",
		"PULLING", "PULL_ERROR", "PULL_SUCCESS",
		"BUILDING", "BUILD_ERROR", "BUILD_SUCCESS",
		"PACKAGING", "PACKAGE_ERROR", "PACKAGE_SUCCESS",
		"PUSHING", "PUSH_ERROR", "PUSH_SUCCESS",
	}[s+3]
}

type task struct {
	id    int
	kind  string
	state string
	time  string
}

type registry struct {
	name     string
	url      string
	user     string
	password string
	login    time.Time
}

type taskRequest struct {
	state   state
	trigger string
}

type project struct {
	id          int
	name        string
	labels      string
	url         string
	branch      string
	destination string
	tag         string
	buildSpec   string
	packageSpec string
	buildHash   []byte
	state       state
	version     int
	tasks       []*task
	queue       chan taskRequest
	triggers    map[*project]state
	prepareDep  *project
	packageDep  *project
}

type broker struct {
	events     chan []byte
	register   chan chan []byte
	unregister chan chan []byte
	clients    map[chan []byte]bool
}

var db *sql.DB
var registries = map[string]*registry{}
var projects = map[int]*project{}
var projectAbs, _ = filepath.Abs("projects")
var clients = &broker{
	make(chan []byte),
	make(chan chan []byte),
	make(chan chan []byte),
	make(map[chan []byte]bool),
}

func registryCreate(name, url, user, password string) *registry {
	db.Exec(`REPLACE INTO registries(name, url, user, password) VALUES(?, ?, ?, ?)`, name, url, user, password)
	logger.Infof("Registry created %s %s %s ******", name, url, user)
	r := &registry{name, url, user, password, time.Unix(0, 0)}
	registries[r.name] = r
	return r
}

func registryLogin(name string) string {
	r := registries[name]
	if r == nil {
		return ""
	}
	if time.Since(r.login).Hours() > 1 {
		if len(r.user) > 0 {
			exec.Command("podman", "login", r.url, "-u", r.user, "-p", r.password).Run()
		}
		r.login = time.Now()
	}
	return r.url
}

func (p *project) buildFrom(state state, trigger string) {
	p.queue <- taskRequest{state, trigger}
}

func projectEvent(event map[string]interface{}) {
	bytes, _ := json.Marshal(event)
	clients.events <- bytes
}

func projectRoutine(p *project) {
	for {
		logger.Infof("Project %d waiting for tasks", p.id)
		request := <-p.queue
		state := request.state
		trigger := request.trigger
		logger.Infof("Project %d received task %s", p.id, state.String())
		command := ""
		args := []string{}
		switch state {
		case CLEANING:
			command = "rm"
			args = []string{"-rfv", fmt.Sprintf("%s/%d/workspace/source", projectAbs, p.id)}
		case CLONING:
			command = "git"
			args = []string{"clone", "-v", "--recursive", "-b", p.branch, p.url, fmt.Sprintf("%s/%d/workspace/source", projectAbs, p.id)}
		case PREPARING:
			command = "podman"
			spec := fmt.Sprintf("%s/%d/%s", projectAbs, p.id, p.buildSpec)
			args = []string{"build", "--squash-all", "-f", spec, "-t", fmt.Sprintf("builder-%d", p.id)}
			if p.prepareDep != nil {
				args = append(args, "--from", fmt.Sprintf("project-%d", p.prepareDep.id))
			}
			args = append(args, fmt.Sprintf("%s/%d/context", projectAbs, p.id))
		case PULLING:
			command = "git"
			args = []string{"-C", fmt.Sprintf("%s/%d/workspace/source", projectAbs, p.id), "pull", "--recurse-submodules"}
		case BUILDING:
			command = "podman"
			args = []string{"run", "--network=host", "--rm=true",
				"-e", fmt.Sprintf("RACS_TRIGGER=%s", trigger),
				"-v", fmt.Sprintf("%s/%d/workspace:/workspace", projectAbs, p.id),
				"--read-only", fmt.Sprintf("builder-%d", p.id),
			}
		case PACKAGING:
			command = "podman"
			spec := fmt.Sprintf("%s/%d/%s", projectAbs, p.id, p.packageSpec)
			args = []string{"build", "-v", fmt.Sprintf("%s/%d/workspace:/workspace", projectAbs, p.id), "--squash", "-f", spec, "-t", fmt.Sprintf("project-%d", p.id)}
			if p.packageDep != nil {
				args = append(args, "--from", fmt.Sprintf("project-%d", p.packageDep.id))
			}
			args = append(args, fmt.Sprintf("%s/%d/context", projectAbs, p.id))
		case PUSHING:
			url := registryLogin(p.destination)
			if len(url) > 0 {
				tag := strings.Replace(p.tag, "$VERSION", strconv.Itoa(p.version), -1)
				command = "podman"
				args = []string{"push", fmt.Sprintf("project-%d", p.id), fmt.Sprintf("%s/%s", url, tag)}
			} else {
				command = "echo"
				args = []string{"no destination"}
			}
		case DELETING:
			command = "rm"
			args = []string{"-vrf", fmt.Sprintf("%s/%d", projectAbs, p.id)}
		}
		p.state = state
		if len(command) > 0 {
			var id int
			var time string
			err := db.QueryRow(`INSERT INTO tasks(project, type, state, time)
				VALUES(?, ?, 'RUNNING', datetime('now')) RETURNING id, time`, p.id, p.state.String()).Scan(&id, &time)
			if err != nil {
				logger.Fatal(err)
			}
			logger.Infof("Creating task %d:%d", p.id, id)
			t := &task{id, p.state.String(), "RUNNING", time}
			p.tasks = append(p.tasks, t)
			if len(p.tasks) > 5 {
				p.tasks = p.tasks[1:]
			}
			projectEvent(map[string]interface{}{
				"event":   "task/create",
				"project": p.id,
				"id":      t.id,
				"type":    t.kind,
				"time":    t.time,
				"state":   "RUNNING",
			})
			taskRoot := fmt.Sprintf("tasks/%d", t.id)
			os.Mkdir(taskRoot, 0777)
			logger.Infof("Task %s %v", command, args)
			cmd := exec.Command(command, args...)
			out, _ := os.Create(fmt.Sprintf("%s/out.log", taskRoot))
			out.WriteString("\u001B[1m")
			out.WriteString(cmd.String())
			out.WriteString("\u001B[0m\n")
			cmd.Stdout = out
			cmd.Stderr = out
			err = cmd.Run()
			if err != nil {
				t.state = "ERROR"
				p.state += 1
			} else {
				t.state = "SUCCESS"
				p.state += 2
			}
			out.Close()
			logger.Infof("Task %d completed", t.id)
			db.Exec(`UPDATE projects SET state = ? WHERE id = ?`, p.state.String(), p.id)
			db.Exec(`UPDATE tasks SET state = ? WHERE id = ?`, t.state, t.id)
			projectEvent(map[string]interface{}{
				"event": "project/state",
				"id":    p.id,
				"state": p.state.String(),
			})
			projectEvent(map[string]interface{}{
				"event":   "task/state",
				"project": p.id,
				"id":      t.id,
				"state":   t.state,
			})
		}
		logger.Infof("Project %d finished task %s", p.id, state.String())
		switch p.state {
		case CREATE_SUCCESS:
			p.buildFrom(CLEANING, trigger)
		case CLEAN_SUCCESS:
			p.buildFrom(CLONING, trigger)
		case CLONE_SUCCESS:
			p.buildFrom(PREPARING, trigger)
		case PREPARE_SUCCESS:
			p.buildFrom(PULLING, trigger)
		case PULL_SUCCESS:
			buildHash := []byte{}
			f, err := os.Open(fmt.Sprintf("%s/%d/%s", projectAbs, p.id, p.buildSpec))
			if err == nil {
				h := sha256.New()
				io.Copy(h, f)
				f.Close()
				buildHash = h.Sum(nil)
			} else {
				logger.Warn(err)
			}
			if !bytes.Equal(buildHash, p.buildHash) {
				p.buildHash = buildHash
				db.Exec(`UPDATE projects SET buildHash = ? WHERE id = ?`, buildHash, p.id)
				p.buildFrom(PREPARING, trigger)
			} else {
				p.buildFrom(BUILDING, trigger)
			}
		case BUILD_SUCCESS:
			p.buildFrom(PACKAGING, trigger)
		case PACKAGE_SUCCESS:
			p.version += 1
			db.Exec(`UPDATE projects SET version = ? WHERE id = ?`, p.version, p.id)
			projectEvent(map[string]interface{}{
				"event":   "project/version",
				"id":      p.id,
				"version": p.version,
			})
			p.buildFrom(PUSHING, trigger)
		case PUSH_SUCCESS:
			tag := strings.Replace(p.tag, "$VERSION", strconv.Itoa(p.version), -1)
			for p2, state2 := range p.triggers {
				p2.buildFrom(state2, tag)
			}
		case DELETE_SUCCESS:
			db.Exec(`DELETE FROM projects WHERE id = ?`, p.id)
			db.Exec(`DELETE FROM tasks WHERE project = ?`, p.id)
			delete(projects, p.id)
			return
		}
	}
}

func projectCreate(name, url, branch, destination, tag string) *project {
	var id int
	db.QueryRow(`INSERT INTO projects(name, source, branch, destination, tag, buildSpec, packageSpec, state, version)
		VALUES(?, ?, ?, ?, ?, 'BuildSpec', 'PackageSpec', 'CLONING', 0) RETURNING id`, name, url, branch, destination, tag).Scan(&id)
	logger.Infof("Project created %s %s %s %s", id, name, url, branch)
	os.Mkdir(fmt.Sprintf("%s/%d", projectAbs, id), 0777)
	os.Mkdir(fmt.Sprintf("%s/%d/context", projectAbs, id), 0777)
	os.Mkdir(fmt.Sprintf("%s/%d/workspace", projectAbs, id), 0777)
	p := &project{
		id, name, "", url, branch, destination, tag, "BuildSpec", "PackageSpec", []byte{},
		CREATE_SUCCESS, 0,
		make([]*task, 0),
		make(chan taskRequest, 10),
		make(map[*project]state),
		nil, nil,
	}
	projects[p.id] = p
	go projectRoutine(p)
	projectEvent(map[string]interface{}{
		"event":       "project/create",
		"id":          p.id,
		"name":        p.name,
		"labels":      p.labels,
		"url":         p.url,
		"branch":      p.branch,
		"destination": p.destination,
		"tag":         p.tag,
		"buildSpec":   p.buildSpec,
		"packageSpec": p.packageSpec,
		"state":       p.state.String(),
		"version":     p.version,
	})
	return p
}

var staticPath, _ = filepath.Abs("static")

func loadStatic(path string) ([]byte, error) {
	path = filepath.Clean(path)
	if path == "." {
		return nil, errors.New("Not found")
	}
	return ioutil.ReadFile(staticPath + path)
}

func projectList() []map[string]interface{} {
	result := make([]map[string]interface{}, 0)
	for id, p := range projects {
		tasks := make([]interface{}, 0)
		for _, task := range p.tasks {
			tasks = append(tasks, map[string]interface{}{
				"id":    task.id,
				"type":  task.kind,
				"state": task.state,
				"time":  task.time,
			})
		}
		triggers := make([]interface{}, 0)
		for target, state := range p.triggers {
			triggers = append(triggers, []interface{}{
				target.id, state.String(),
			})
		}
		result = append(result, map[string]interface{}{
			"id":          id,
			"name":        p.name,
			"labels":      p.labels,
			"url":         p.url,
			"branch":      p.branch,
			"destination": p.destination,
			"tag":         p.tag,
			"buildSpec":   p.buildSpec,
			"packageSpec": p.packageSpec,
			"state":       p.state.String(),
			"tasks":       tasks,
			"version":     p.version,
			"triggers":    triggers,
		})
	}
	sort.Slice(result, func(i, j int) bool {
		return result[i]["id"].(int) < result[j]["id"].(int)
	})
	return result
}

var ciph cipher.Block

type user struct {
	Name  string
	Roles []string
}

func renderLogin(w http.ResponseWriter, path string, params map[string]string) {
	loginTemplate, _ := template.ParseFiles(staticPath + "/login.xhtml")
	w.Header().Add("Content-Type", "application/xhtml+xml")
	var sb strings.Builder
	sep := ""
	for name, value := range params {
		sb.WriteString(sep)
		sb.WriteString(url.QueryEscape(name))
		sb.WriteRune('=')
		sb.WriteString(url.QueryEscape(value))
		sep = "&"
	}
	err := loginTemplate.Execute(w, map[string]interface{}{
		"action": path,
		"params": sb.String(),
	})
	if err != nil {
		logger.Error(err)
	}
}

func renderDenied(w http.ResponseWriter, path string, params map[string]string) {

}

var noLogin bool = false

func checkLogin(u *user, role string, w http.ResponseWriter, path string, params map[string]string) bool {
	if noLogin {
		return false
	}
	for _, r := range u.Roles {
		if r == role {
			return false
		}
	}
	renderLogin(w, path, params)
	return true
}

func handleUserLogin(w http.ResponseWriter, r *http.Request, u *user, params map[string]string) {
	username := params["username"]
	password := params["password"]
	tr, err := pam.StartFunc("sudo", username, func(s pam.Style, msg string) (string, error) {
		switch s {
		case pam.PromptEchoOn:
			return username, nil
		case pam.PromptEchoOff:
			return password, nil
		}
		return "", errors.New("Unrecognized message")
	})
	if err != nil {
		logger.Error(err)
	}
	err = tr.SetItem(pam.Ruser, username)
	if err != nil {
		logger.Error(err)
	}
	err = tr.Authenticate(0)
	if err != nil {
		logger.Error(err)
		w.WriteHeader(401)
		w.Write([]byte(err.Error()))
		return
	}
	u2 := user{username, []string{"admin", "user"}}
	gcm, _ := cipher.NewGCM(ciph)
	nonceSize := gcm.NonceSize()
	nonce := make([]byte, nonceSize)
	rand.Read(nonce)
	in, _ := json.Marshal(u2)
	en := gcm.Seal(nil, nonce, in, nil)
	out := make([]byte, len(en)+nonceSize)
	copy(out[:nonceSize], nonce)
	copy(out[nonceSize:], en)
	cookie := http.Cookie{
		Name:    "RACS_TOKEN",
		Value:   hex.EncodeToString(out),
		Path:    "/",
		Expires: time.Now().Add(24 * time.Hour),
	}
	http.SetCookie(w, &cookie)
	action := params["action"]
	redirect := params["redirect"]
	if len(action) > 0 {
		query, _ := url.ParseQuery(params["params"])
		params := make(map[string]string)
		for name, values := range query {
			params[name] = values[0]
		}
		handleAction(action, w, r, &u2, params)
	} else if len(redirect) > 0 {
		w.Header().Add("Location", redirect)
		w.WriteHeader(303)
	} else {
		w.WriteHeader(200)
		w.Write([]byte(username))
	}
}

func handleUserLogout(w http.ResponseWriter, r *http.Request, u *user, params map[string]string) {
	cookie := http.Cookie{
		Name:    "RACS_TOKEN",
		Value:   "",
		Path:    "/",
		Expires: time.Unix(0, 0),
	}
	http.SetCookie(w, &cookie)
	redirect := params["redirect"]
	if len(redirect) > 0 {
		w.Header().Add("Location", redirect)
		w.WriteHeader(303)
	} else {
		w.WriteHeader(200)
		w.Write([]byte("OK"))
	}
}

func handleUserCurrent(w http.ResponseWriter, r *http.Request, u *user, params map[string]string) {
	w.WriteHeader(200)
	w.Write([]byte(u.Name))
}

func handleProjectList(w http.ResponseWriter, r *http.Request, u *user, params map[string]string) {
	result := projectList()
	w.Header().Add("Content-Type", "application/json")
	j, _ := json.Marshal(result)
	w.Write(j)
}

func handleProjectEvents(w http.ResponseWriter, r *http.Request, u *user, params map[string]string) {
	flusher, ok := w.(http.Flusher)
	if !ok {
		http.Error(w, "Streaming unsupported!", http.StatusInternalServerError)
		return
	}
	w.Header().Set("Content-Type", "text/event-stream")
	w.Header().Set("Cache-Control", "no-cache")
	w.Header().Set("Connection", "keep-alive")
	w.Header().Set("Access-Control-Allow-Origin", "*")
	events := make(chan []byte)
	clients.register <- events
	defer func() {
		clients.unregister <- events
	}()
	notify := w.(http.CloseNotifier).CloseNotify()
	go func() {
		<-notify
		clients.unregister <- events
	}()
	j, _ := json.Marshal(map[string]interface{}{
		"event":    "project/list",
		"projects": projectList(),
	})
	fmt.Fprintf(w, "data: %s\n\n", j)
	flusher.Flush()
	for {
		fmt.Fprintf(w, "data: %s\n\n", <-events)
		flusher.Flush()
	}
}

func handleProjectStatus(w http.ResponseWriter, r *http.Request, u *user, params map[string]string) {
	id, _ := strconv.Atoi(params["id"])
	p := projects[id]
	if p == nil {
		w.WriteHeader(500)
	} else {
		w.Header().Add("Content-Type", "application/json")
		j, _ := json.Marshal(map[string]interface{}{
			"id":          id,
			"name":        p.name,
			"url":         p.url,
			"branch":      p.branch,
			"destination": p.destination,
			"buildSpec":   p.buildSpec,
			"packageSpec": p.packageSpec,
			"tag":         p.tag,
			"labels":      p.labels,
		})
		w.Write(j)
	}
}

func handleProjectUpdate(w http.ResponseWriter, r *http.Request, u *user, params map[string]string) {
	if checkLogin(u, "admin", w, "/project/update", params) {
		return
	}
	id, _ := strconv.Atoi(params["id"])
	p := projects[id]
	if p == nil {
		w.WriteHeader(500)
	} else {
		p.name = params["name"]
		p.labels = params["labels"]
		p.url = params["url"]
		p.branch = params["branch"]
		p.destination = params["destination"]
		p.tag = params["tag"]
		p.buildSpec = filepath.Clean(params["buildSpec"])
		p.packageSpec = filepath.Clean(params["packageSpec"])
		db.Exec(`UPDATE projects SET name = ?, labels = ?, source = ?, branch = ?, destination = ?, tag = ?,
			buildSpec = ?, packageSpec = ? WHERE id = ?`,
			p.name, p.labels, p.url, p.branch, p.destination, p.tag, p.buildSpec, p.packageSpec, p.id)
		projectEvent(map[string]interface{}{
			"event":       "project/update",
			"id":          p.id,
			"name":        p.name,
			"labels":      p.labels,
			"url":         p.url,
			"branch":      p.branch,
			"destination": p.destination,
			"buildSpec":   p.buildSpec,
			"packageSpec": p.packageSpec,
			"tag":         p.tag,
		})
		redirect := params["redirect"]
		if len(redirect) > 0 {
			w.Header().Add("Location", redirect)
			w.WriteHeader(303)
		} else {
			w.WriteHeader(200)
			w.Write([]byte("OK"))
		}
	}
}

func handleProjectCreate(w http.ResponseWriter, r *http.Request, u *user, params map[string]string) {
	if checkLogin(u, "admin", w, "/project/create", params) {
		return
	}
	name := params["name"]
	url := params["url"]
	branch := params["branch"]
	destination := params["destination"]
	tag := params["tag"]
	p := projectCreate(name, url, branch, destination, tag)
	redirect := params["redirect"]
	if len(redirect) > 0 {
		w.Header().Add("Location", redirect)
		w.WriteHeader(303)
	} else {
		w.WriteHeader(201)
		w.Write([]byte(strconv.Itoa(p.id)))
	}
}

func handleProjectUpload(w http.ResponseWriter, r *http.Request, u *user, params map[string]string) {
	if r.MultipartForm != nil {
		files := r.MultipartForm.File["file"]
		if (files != nil) && (len(files) > 0) {
			file := files[0]
			temp, _ := ioutil.TempFile("uploads", "upload-")
			rd, _ := file.Open()
			io.Copy(temp, rd)
			temp.Close()
			rd.Close()
			params["upload"] = temp.Name()
		}
	}
	if params["value"] != "" {
		temp, _ := ioutil.TempFile("uploads", "upload-")
		temp.WriteString(params["value"])
		temp.Close()
		params["upload"] = temp.Name()
	}
	if checkLogin(u, "admin", w, "/project/upload", params) {
		return
	}
	id, _ := strconv.Atoi(params["id"])
	name := filepath.Clean(params["name"])
	upload := filepath.Clean(params["upload"])
	validUpload, _ := regexp.MatchString("^uploads/upload-[0-9]+$", upload)
	p := projects[id]
	if p == nil {
		w.WriteHeader(500)
	} else if name == "." {
		w.WriteHeader(500)
	} else if !validUpload {
		w.WriteHeader(500)
	} else {
		err := os.Rename(upload, fmt.Sprintf("%s/%d/%s", projectAbs, id, name))
		if err != nil {
			logger.Error(err)
		}
		redirect := params["redirect"]
		if len(redirect) > 0 {
			w.Header().Add("Location", redirect)
			w.WriteHeader(303)
		} else {
			w.WriteHeader(200)
			w.Write([]byte("OK"))
		}
	}
}

func handleProjectTriggers(w http.ResponseWriter, r *http.Request, u *user, params map[string]string) {
	if checkLogin(u, "admin", w, "/project/triggers", params) {
		return
	}
	pid, _ := strconv.Atoi(params["id"])
	p := projects[pid]
	for target, state := range p.triggers {
		switch state {
		case PREPARING:
			target.prepareDep = nil
		case PACKAGING:
			target.packageDep = nil
		}
	}
	p.triggers = make(map[*project]state)
	db.Exec(`DELETE FROM triggers WHERE project = ?`, p.id)
	triggers := strings.FieldsFunc(params["triggers"], func(c rune) bool {
		return c == ','
	})
	for i := 0; i < len(triggers); i += 2 {
		tid, _ := strconv.Atoi(triggers[i])
		t := projects[tid]
		s := NONE
		switch triggers[i+1] {
		case "clean":
			s = CLEANING
		case "clone":
			s = CLONING
		case "prepare":
			s = PREPARING
			t.prepareDep = p
		case "pull":
			s = PULLING
		case "build":
			s = BUILDING
		case "package":
			s = PACKAGING
			t.packageDep = p
		case "push":
			s = PUSHING
		}
		p.triggers[t] = s
		db.Exec(`INSERT INTO triggers(project, target, state) VALUES(?, ?, ?)`, p.id, t.id, s.String())
	}
	redirect := params["redirect"]
	if len(redirect) > 0 {
		w.Header().Add("Location", redirect)
		w.WriteHeader(303)
	} else {
		w.WriteHeader(200)
		w.Write([]byte("OK"))
	}
}

func handleProjectBuild(w http.ResponseWriter, r *http.Request, u *user, params map[string]string) {
	id, _ := strconv.Atoi(params["id"])
	stage := params["stage"]
	p := projects[id]
	switch stage {
	case "clean":
		p.buildFrom(CLEANING, "")
	case "clone":
		p.buildFrom(CLONING, "")
	case "prepare":
		p.buildFrom(PREPARING, "")
	case "pull":
		p.buildFrom(PULLING, "")
	case "build":
		p.buildFrom(BUILDING, "")
	case "package":
		p.buildFrom(PACKAGING, "")
	case "push":
		p.buildFrom(PUSHING, "")
	}
	w.WriteHeader(200)
	w.Write([]byte("OK"))
}

func handleProjectDelete(w http.ResponseWriter, r *http.Request, u *user, params map[string]string) {
	id, _ := strconv.Atoi(params["id"])
	confirm := params["confirm"]
	if confirm == "YES" {
		projects[id].buildFrom(DELETING, "")
	}
	redirect := params["redirect"]
	if len(redirect) > 0 {
		w.Header().Add("Location", redirect)
		w.WriteHeader(303)
	} else {
		w.WriteHeader(200)
		w.Write([]byte("OK"))
	}
}

func handleTaskLogs(w http.ResponseWriter, r *http.Request, u *user, params map[string]string) {
	id, _ := strconv.Atoi(params["id"])
	var state string
	db.QueryRow(`SELECT state FROM tasks WHERE id = ?`, id).Scan(&state)
	offset, _ := strconv.ParseInt(params["offset"], 10, 64)
	file, _ := os.Open(fmt.Sprintf("tasks/%d/out.log", id))
	file.Seek(offset, 0)
	bytes, _ := ioutil.ReadAll(file)
	w.Header().Add("Content-Type", "text/plain")
	w.Header().Add("X-Task-State", state)
	w.Write(bytes)
}

func handleRegistryCreate(w http.ResponseWriter, r *http.Request, u *user, params map[string]string) {
	if checkLogin(u, "admin", w, "/registry/create", params) {
		return
	}
	name := params["name"]
	url := params["url"]
	user := params["user"]
	password := params["password"]
	reg := registryCreate(name, url, user, password)
	redirect := params["redirect"]
	if len(redirect) > 0 {
		w.Header().Add("Location", redirect)
		w.WriteHeader(303)
	} else {
		w.WriteHeader(201)
		w.Write([]byte(reg.name))
	}
}

func handleAction(path string, w http.ResponseWriter, r *http.Request, u *user, params map[string]string) bool {
	switch path {
	case "/user/current":
		handleUserCurrent(w, r, u, params)
	case "/user/login":
		handleUserLogin(w, r, u, params)
	case "/user/logout":
		handleUserLogout(w, r, u, params)
	case "/project/list":
		handleProjectList(w, r, u, params)
	case "/project/status":
		handleProjectStatus(w, r, u, params)
	case "/project/events":
		handleProjectEvents(w, r, u, params)
	case "/project/update":
		handleProjectUpdate(w, r, u, params)
	case "/project/triggers":
		handleProjectTriggers(w, r, u, params)
	case "/project/create":
		handleProjectCreate(w, r, u, params)
	case "/project/upload":
		handleProjectUpload(w, r, u, params)
	case "/project/build":
		handleProjectBuild(w, r, u, params)
	case "/project/delete":
		handleProjectDelete(w, r, u, params)
	case "/task/logs":
		handleTaskLogs(w, r, u, params)
	case "/registry/create":
		handleRegistryCreate(w, r, u, params)
	default:
		return false
	}
	return true
}

func handleRoot(w http.ResponseWriter, r *http.Request) {
	logger.Infof("%s %s %s", r.Method, r.RemoteAddr, r.URL.Path)
	contentType := r.Header.Get("Content-Type")
	params := make(map[string]string)
	if strings.HasPrefix(contentType, "application/json") {
		body, _ := ioutil.ReadAll(r.Body)
		var j map[string]interface{}
		json.Unmarshal(body, &j)
		for name, value := range j {
			params[name] = fmt.Sprint(value)
		}
	} else if strings.HasPrefix(contentType, "multipart/form-data") {
		r.ParseMultipartForm(10000000)
		for name, values := range r.MultipartForm.Value {
			params[name] = values[0]
		}
	} else {
		r.ParseForm()
		for name, values := range r.Form {
			params[name] = values[0]
		}
	}
	u := user{"", []string{}}
	if noLogin {
		u.Name = "user"
	}
	cookie, err := r.Cookie("RACS_TOKEN")
	if cookie != nil {
		b, _ := hex.DecodeString(cookie.Value)
		gcm, _ := cipher.NewGCM(ciph)
		nonceSize := gcm.NonceSize()
		nonce, in := b[:nonceSize], b[nonceSize:]
		de, _ := gcm.Open(nil, nonce, in, nil)
		json.Unmarshal(de, &u)
	}
	path := r.URL.Path
	if handleAction(path, w, r, &u, params) {
		return
	}
	if path == "/" {
		path = "/index.xhtml"
	}
	switch filepath.Ext(path) {
	case ".xhtml":
		contentType = "application/xhtml+xml"
	case ".js":
		contentType = "text/javascript"
	case ".css":
		contentType = "text/css"
	case ".ico":
		contentType = "image/png"
	default:
		contentType = ""
	}
	content, err := loadStatic(path)
	if err != nil {
		w.WriteHeader(404)
		w.Write([]byte("Not found"))
	} else {
		w.Header().Add("Content-Type", contentType)
		w.Write(content)
	}
}

func main() {
	var sslCert, sslKey string
	var port int
	flag.StringVar(&sslCert, "ssl-cert", "", "SSL cert")
	flag.StringVar(&sslKey, "ssl-key", "", "SSL key")
	flag.BoolVar(&noLogin, "no-login", false, "Allow all actions without login")
	flag.IntVar(&port, "port", 8080, "Web server port")
	flag.Parse()

	key := make([]byte, 32)
	rand.Read(key)
	ciph, _ = aes.NewCipher(key)

	var err error

	os.Mkdir("projects", 0777)
	os.Mkdir("tasks", 0777)
	os.Mkdir("uploads", 0777)
	os.Setenv("GIT_TERMINAL_PROMPT", "0")

	db, err = sql.Open("sqlite3", "file:main.db?cache=shared")
	if err != nil {
		logger.Fatal(err)
	}
	defer db.Close()
	//db.SetMaxOpenConns(1)

	stats := []string{
		`CREATE TABLE IF NOT EXISTS users(
			name STRING PRIMARY KEY,
			passwd STRING,
			salt STRING,
			role STRING
		)`,
		`CREATE TABLE IF NOT EXISTS registries(
			name STRING PRIMARY KEY,
			url STRING,
			user STRING,
			password STRING
		)`,
		`CREATE TABLE IF NOT EXISTS projects(
			id INTEGER PRIMARY KEY,
			name STRING,
			source STRING,
			branch STRING,
			destination STRING,
			tag STRING,
			buildSpec STRING,
			packageSpec STRING,
			state STRING,
			version INTEGER
		)`,
		`ALTER TABLE projects ADD COLUMN buildHash BLOB`,
		`ALTER TABLE projects ADD COLUMN labels STRING`,
		`CREATE TABLE IF NOT EXISTS tasks(
			id INTEGER PRIMARY KEY,
			project INTEGER,
			type STRING,
			state STRING,
			time STRING
		)`,
		`CREATE TABLE IF NOT EXISTS members(
			project INTEGER,
			user STRING,
			role STRING
		)`,
		`CREATE TABLE IF NOT EXISTS triggers(
			project INTEGER,
			target INTEGER,
			state STRING
		)`,
	}

	for _, stat := range stats {
		db.Exec(stat)
	}

	states := make(map[string]state)
	for state := DELETING; state <= PUSH_SUCCESS; state += 1 {
		states[state.String()] = state
	}

	rows, err := db.Query(`SELECT name, url, user, password FROM registries`)
	for rows.Next() {
		var name string
		var url string
		var user string
		var password string
		rows.Scan(&name, &url, &user, &password)
		registries[name] = &registry{name, url, user, password, time.Unix(0, 0)}
	}
	rows, err = db.Query(`SELECT id, name, labels, source, branch, destination, tag, buildSpec, packageSpec, buildHash, state, version FROM projects`)
	for rows.Next() {
		var id int
		var name string
		var source string
		var branch string
		var destination string
		var tag string
		var buildSpec string
		var packageSpec string
		var buildHash []byte
		var labels string
		var stateName string
		var version int
		rows.Scan(&id, &name, &labels, &source, &branch, &destination, &tag, &buildSpec, &packageSpec, &buildHash, &stateName, &version)
		p := &project{
			id, name, labels, source, branch, destination, tag, buildSpec, packageSpec, buildHash,
			states[stateName], version,
			make([]*task, 0),
			make(chan taskRequest, 10),
			make(map[*project]state),
			nil, nil,
		}
		projects[p.id] = p
		go projectRoutine(p)
	}
	rows, err = db.Query(`SELECT project, id, type, state, time FROM tasks ORDER BY id`)
	for rows.Next() {
		var pid int
		var id int
		var kind string
		var state string
		var time string
		rows.Scan(&pid, &id, &kind, &state, &time)
		p := projects[pid]
		if p != nil {
			p.tasks = append(p.tasks, &task{id, kind, state, time})
			if len(p.tasks) > 5 {
				p.tasks = p.tasks[1:]
			}
		}
	}
	rows, err = db.Query(`SELECT project, target, state FROM triggers`)
	for rows.Next() {
		var pid int
		var tid int
		var stateName string
		rows.Scan(&pid, &tid, &stateName)
		p := projects[pid]
		t := projects[tid]
		if p != nil && t != nil {
			p.triggers[t] = states[stateName]
			switch states[stateName] {
			case PREPARING:
				t.prepareDep = p
			case PACKAGING:
				t.packageDep = p
			}
		}
	}

	go func() {
		for {
			select {
			case client := <-clients.register:
				clients.clients[client] = true
			case client := <-clients.unregister:
				delete(clients.clients, client)
			case event := <-clients.events:
				for client, _ := range clients.clients {
					client <- event
				}
			}
		}
	}()

	go func() {
		for {
			logger.Info("Pruning images")
			err := exec.Command("podman", "image", "prune", "-f", "--filter", "until=5m").Run()
			if err != nil {
				logger.Error(err)
			}
			time.Sleep(60 * time.Second)
		}
	}()

	http.HandleFunc("/", handleRoot)
	endpoint := fmt.Sprintf(":%d", port)
	if len(sslCert) > 0 {
		logger.Infof("Listening on https://0.0.0.0:%d", port)
		logger.Fatal(http.ListenAndServeTLS(endpoint, sslCert, sslKey, nil))
	} else {
		logger.Infof("Listening on http://0.0.0.0:%d", port)
		logger.Fatal(http.ListenAndServe(endpoint, nil))
	}
}
