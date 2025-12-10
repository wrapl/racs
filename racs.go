package main

import (
	"bufio"
	"bytes"
	"context"
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
	"slices"
	"sort"
	"strconv"
	"strings"
	"sync"
	"text/template"
	"time"

	"github.com/goccy/go-graphviz"
	"github.com/goccy/go-graphviz/cgraph"
	_ "github.com/mattn/go-sqlite3"
	"github.com/msteinert/pam"
	"github.com/withmandala/go-log"
	"github.com/xhit/go-str2duration/v2"
	"golang.org/x/sync/semaphore"
)

var logger = log.New(os.Stderr)

type state int

const (
	DELETING           state = -3
	DELETE_ERROR       state = -2
	DELETE_SUCCESS     state = -1
	NONE               state = 0
	CREATING           state = 1
	CREATE_ERROR       state = 2
	CREATE_SUCCESS     state = 3
	CLEANING           state = 4
	CLEAN_ERROR        state = 5
	CLEAN_SUCCESS      state = 6
	CLONING            state = 7
	CLONE_ERROR        state = 8
	CLONE_SUCCESS      state = 9
	PREPARING          state = 10
	PREPARE_ERROR      state = 11
	PREPARE_SUCCESS    state = 12
	PULLING            state = 13
	PULL_ERROR         state = 14
	PULL_SUCCESS       state = 15
	BUILDING           state = 16
	BUILD_ERROR        state = 17
	BUILD_SUCCESS      state = 18
	PREPACKAGING       state = 19
	PREPACKAGE_ERROR   state = 20
	PREPACKAGE_SUCCESS state = 21
	PACKAGING          state = 22
	PACKAGE_ERROR      state = 23
	PACKAGE_SUCCESS    state = 24
	SCANNING           state = 25
	SCAN_ERROR         state = 26
	SCAN_SUCCESS       state = 27
	PUSHING            state = 28
	PUSH_ERROR         state = 29
	PUSH_SUCCESS       state = 30
	TAGGING            state = 31
	TAG_ERROR          state = 32
	TAG_SUCCESS        state = 33
)

func (s state) String() string {
	return [TAG_SUCCESS + 1 - DELETING]string{
		"DELETING", "DELETE_ERROR", "DELETE_SUCCESS",
		"NONE",
		"CREATING", "CREATE_ERROR", "CREATE_SUCCESS",
		"CLEANING", "CLEAN_ERROR", "CLEAN_SUCCESS",
		"CLONING", "CLONE_ERROR", "CLONE_SUCCESS",
		"PREPARING", "PREPARE_ERROR", "PREPARE_SUCCESS",
		"PULLING", "PULL_ERROR", "PULL_SUCCESS",
		"BUILDING", "BUILD_ERROR", "BUILD_SUCCESS",
		"PREPACKAGING", "PREPACKAGE_ERROR", "PREPACKAGE_SUCCESS",
		"PACKAGING", "PACKAGE_ERROR", "PACKAGE_SUCCESS",
		"SCANNING", "SCAN_ERROR", "SCAN_SUCCESS",
		"PUSHING", "PUSH_ERROR", "PUSH_SUCCESS",
		"TAGGING", "TAG_ERROR", "TAG_SUCCESS",
	}[s-DELETING]
}

type task struct {
	id    int
	kind  state
	state string
	time  time.Time
}

type registry struct {
	id         int
	name       string
	url        string
	user       string
	credential int
	login      time.Time
	timeout    int
}

type taskRequest struct {
	state   state
	from    state
	trigger map[string]string
	index   int
	force   bool
}

type credential struct {
	id          int
	name        string
	value       string
	project     int
	request     string
	expiry      time.Time
	updated     time.Time
	description string
}

type destination struct {
	registry *registry
	tag      string
}

type trigger struct {
	from   state
	states map[state]bool
}

type project struct {
	id             int
	name           string
	labels         string
	url            string
	branch         string
	buildSpec      string
	prepackageSpec string
	packageSpec    string
	buildHash      []byte
	state          state
	version        int
	protected      bool
	destinations   []destination
	sources        map[string]*registry
	tasks          []*task
	queue          chan taskRequest
	triggers       map[*project]trigger
	credentials    map[string]*credential
	prepareDep     *project
	prepackageDep  *project
	packageDep     *project
	scanners       []*project
	commit         string
	tag            string
	group          string
}

type broker struct {
	events     chan []byte
	register   chan chan []byte
	unregister chan chan []byte
	clients    map[chan []byte]bool
}

var db *sql.DB
var registries = map[int]*registry{}
var credentials = map[int]*credential{}
var projects = map[int]*project{}
var activeCommands = map[int]*exec.Cmd{}
var projectAbs, _ = filepath.Abs("projects")
var clients = &broker{
	make(chan []byte),
	make(chan chan []byte),
	make(chan chan []byte),
	make(map[chan []byte]bool),
}

func event(event map[string]interface{}) {
	bytes, _ := json.Marshal(event)
	clients.events <- bytes
}

func registryList() []map[string]interface{} {
	result := make([]map[string]interface{}, 0)
	for id, r := range registries {
		result = append(result, map[string]interface{}{
			"id":         id,
			"name":       r.name,
			"url":        r.url,
			"user":       r.user,
			"credential": r.credential,
			"timeout":    r.timeout,
			"login":      r.login.Unix(),
		})
	}
	return result
}

func registryCreate(name, url, user string, credential, timeout int) *registry {
	var id int
	db.QueryRow(`INSERT INTO registries(name, url, user, credential, timeout) VALUES(?, ?, ?, ?, ?) RETURNING id`,
		name, url, user, credential, timeout).Scan(&id)
	logger.Infof("Registry created %s %s %s ******", name, url, user)
	r := &registry{id, name, url, user, credential, time.Unix(0, 0), timeout}
	registries[r.id] = r
	return r
}

func registryLogin(r *registry) (bool, string) {
	if time.Since(r.login).Minutes() > float64(r.timeout) {
		if len(r.user) > 0 {
			cr := credentials[r.credential]
			logger.Infof("Logging into registry %s -> %s", r.url, cr.name)
			out, err := exec.Command("podman", "login", r.url, "-u", r.user, "-p", credentialValue(cr)).CombinedOutput()
			if err != nil {
				return false, string(out)
			}
		}
		r.login = time.Now()
	}
	return true, r.url
}

func (p *project) buildFrom(state state, trigger map[string]string, force bool) {
	p.queue <- taskRequest{state, state, trigger, 0, force}
}

func projectEnvironment(p *project, request taskRequest) string {
	filename := fmt.Sprintf("%s/%d/environment", projectAbs, p.id)
	f, _ := os.Create(filename)
	trigger := request.trigger
	for name, value := range trigger {
		fmt.Fprintf(f, "RACS_TRIGGER_%s=%s\n", name, value)
	}
	if value, ok := trigger["TAG"]; ok {
		fmt.Fprintf(f, "RACS_TRIGGER=%s\n", value)
	}
	if value, ok := trigger["VERSION"]; ok {
		fmt.Fprintf(f, "RACS_VERSION=%s\n", value)
	}
	for name, cr := range p.credentials {
		fmt.Fprintf(f, "%s=%s\n", name, credentialValue(cr))
	}
	f.Close()
	return filename
}

var jobSemaphore *semaphore.Weighted
var fromPattern = regexp.MustCompile("^FROM ([^/]*).*$")

func registryBySpec(spec string) *registry {
	f, err := os.Open(spec)
	if err != nil {
		return nil
	}
	defer f.Close()
	s := bufio.NewScanner(f)
	for s.Scan() {
		from := fromPattern.FindStringSubmatch(s.Text())
		if from != nil {
			for _, r := range registries {
				if from[1] == r.url {
					return r
				}
			}
		}
	}
	return nil
}

func registryLoginBySpec(spec string) (bool, string) {
	r := registryBySpec(spec)
	if r == nil {
		return true, ""
	}
	ok, msg := registryLogin(r)
	if !ok {
		return false, msg
	}
	return true, r.url
}

var projectStateMutex sync.Mutex
var projectStateCond = sync.NewCond(&projectStateMutex)

func lastTask(p *project, st state, after time.Time) *task {
	for i := len(p.tasks) - 1; i >= 0; i-- {
		t := p.tasks[i]
		logger.Infof("Found task %s -> %s", t.kind.String(), t.state)
		if t.time.After(after) {
			switch t.state {
			case "ERROR":
				return t
			case "STOPPED":
				return t
			case "QUEUE":
				return nil
			case "RUNNING":
				return nil
			case "SUCCESS":
				if t.kind == st {
					return t
				}
			}
		}
	}
	return nil
}

func credentialValue(cr *credential) string {
	if cr.project > 0 && cr.expiry.Before(time.Now()) {
		p := projects[cr.project]
		start := time.Now()
		trigger := map[string]string{
			"CREDENTIAL": cr.name,
			"REQUEST":    cr.request,
		}
		p.buildFrom(PULLING, trigger, false)
		projectStateMutex.Lock()
		t := lastTask(p, BUILDING, start)
		for t == nil {
			projectStateCond.Wait()
			t = lastTask(p, BUILDING, start)
		}
		projectStateMutex.Unlock()
		if t.state == "SUCCESS" {
			in, err := os.Open(fmt.Sprintf("tasks/%d/out.log", t.id))
			if err != nil {
				return "<Error opening log file>"
			}
			defer in.Close()
			s := bufio.NewScanner(in)
			var value = ""
			var duration = ""
			for s.Scan() {
				line := s.Text()
				if strings.HasPrefix(line, "RACS_CREDENTIAL_VALUE ") {
					value = line[22:]
				} else if strings.HasPrefix(line, "RACS_CREDENTIAL_EXPIRY ") {
					duration = line[23:]
				}
			}
			cr.value = value
			if duration != "" {
				d, _ := str2duration.ParseDuration(duration)
				cr.expiry = t.time.Add(d)
			}
			now := time.Now()
			db.Exec(`UPDATE credentials SET value = ?, expiry = ?, updated = ? WHERE id = ?`, credentialEncrypt(cr.value), cr.expiry.Unix(), now.Unix(), cr.id)
		} else {
			return "<Error building project>"
		}
	}
	return cr.value
}

func projectRoutine(p *project) {
	os.Mkdir(fmt.Sprintf("%s/%d/context", projectAbs, p.id), 0777)
	os.Mkdir(fmt.Sprintf("%s/%d/workspace", projectAbs, p.id), 0777)
	os.Mkdir(fmt.Sprintf("%s/%d/config", projectAbs, p.id), 0777)
	exec.Command("git", "-C", fmt.Sprintf("%s/%d/workspace/source", projectAbs, p.id), "remote", "set-url", "origin", p.url).Output()
	logger.Infof("Project %d waiting for tasks", p.id)
	request := <-p.queue
	for {
		state := request.state
		logger.Infof("Project %d received task %s", p.id, state.String())
		command := ""
		dir := ""
		args := []string{}
		env := []string{}
		switch state {
		case CLEANING:
			command = "rm"
			args = []string{"-rfv", fmt.Sprintf("%s/%d/workspace/source", projectAbs, p.id)}
		case CLONING:
			command = "git"
			args = []string{"clone", "-v", "--recursive", "-b", p.branch, p.url, fmt.Sprintf("%s/%d/workspace/source", projectAbs, p.id)}
		case PREPARING:
			if p.buildSpec != "" {
				spec := fmt.Sprintf("%s/%d/%s", projectAbs, p.id, p.buildSpec)
				ok := true
				url := ""
				if r := registryBySpec(spec); r != nil {
					p.sources["Build"] = r
					ok, url = registryLogin(r)
				} else {
					delete(p.sources, "Build")
				}
				if ok {
					command = "podman"
					args = []string{"build",
						"--build-arg-file", projectEnvironment(p, request),
						"--squash",
						"-f", spec,
						"-t", fmt.Sprintf("builder-%d", p.id),
					}
					if p.prepareDep != nil {
						args = append(args, "--from", fmt.Sprintf("package-%d", p.prepareDep.id))
					} else {
						args = append(args, "--pull=always") // Work around podman issue https://github.com/containers/podman/issues/22845 "--pull=newer"
					}
					args = append(args, fmt.Sprintf("%s/%d/context", projectAbs, p.id))
				} else {
					command = "error"
					args = []string{url}
				}
			} else {
				command = "echo"
				args = []string{"skipping prepare"}
			}
		case PULLING:
			command = "git"
			args = []string{"-C", fmt.Sprintf("%s/%d/workspace/source", projectAbs, p.id), "pull", "--recurse-submodules"}
		case BUILDING:
			if p.buildSpec != "" {
				command = "podman"
				args = []string{"run", "--network=host", "--rm=true",
					"--env-file", projectEnvironment(p, request),
					"-v", fmt.Sprintf("%s/%d/workspace:/workspace", projectAbs, p.id),
					"-v", fmt.Sprintf("%s/%d/config:/config", projectAbs, p.id),
					"--read-only", fmt.Sprintf("builder-%d", p.id),
				}
			} else {
				command = "echo"
				args = []string{"skipping build"}
			}
		case PREPACKAGING:
			if p.prepackageSpec != "" {
				spec := fmt.Sprintf("%s/%d/%s", projectAbs, p.id, p.prepackageSpec)
				ok := true
				url := ""
				if r := registryBySpec(spec); r != nil {
					p.sources["Prepackage"] = r
					ok, url = registryLogin(r)
				} else {
					delete(p.sources, "Prepackage")
				}
				if ok {
					command = "podman"
					cache_ttl := "24h"
					if request.force {
						cache_ttl = "0"
					}
					args = []string{"build",
						"-v", fmt.Sprintf("%s/%d/workspace:/workspace", projectAbs, p.id),
						"-v", fmt.Sprintf("%s/%d/config:/config", projectAbs, p.id),
						"--build-arg-file", projectEnvironment(p, request),
						"--layers",
						fmt.Sprintf("--cache-ttl=%s", cache_ttl),
						"-f", spec,
						"-t", fmt.Sprintf("prepackage-%d", p.id),
					}
					if p.prepackageDep != nil {
						args = append(args, "--from", fmt.Sprintf("package-%d", p.prepackageDep.id))
					} else {
						args = append(args, "--pull=always") // Work around podman issue https://github.com/containers/podman/issues/22845 "--pull=newer"
					}
					args = append(args, fmt.Sprintf("%s/%d/workspace", projectAbs, p.id))
				} else {
					command = "error"
					args = []string{url}
				}
			} else {
				command = "echo"
				args = []string{"skipping prepackage"}
			}
		case PACKAGING:
			if p.packageSpec != "" {
				spec := fmt.Sprintf("%s/%d/%s", projectAbs, p.id, p.packageSpec)
				ok := true
				url := ""
				if p.prepackageSpec == "" {
					if r := registryBySpec(spec); r != nil {
						p.sources["Package"] = r
						ok, url = registryLogin(r)
					} else {
						delete(p.sources, "Package")
					}
				}
				if ok {
					command = "podman"
					args = []string{"build",
						"-v", fmt.Sprintf("%s/%d/workspace:/workspace", projectAbs, p.id),
						"-v", fmt.Sprintf("%s/%d/config:/config", projectAbs, p.id),
						"--build-arg-file", projectEnvironment(p, request),
						"--squash",
						"-f", spec,
						"-t", fmt.Sprintf("package-%d", p.id),
					}
					if p.packageDep != nil {
						args = append(args, "--from", fmt.Sprintf("package-%d", p.packageDep.id))
					} else if p.prepackageSpec != "" {
						args = append(args, "--from", fmt.Sprintf("prepackage-%d", p.id))
					} else {
						args = append(args, "--pull=always") // Work around podman issue https://github.com/containers/podman/issues/22845 "--pull=newer"
					}
					args = append(args, fmt.Sprintf("%s/%d/context", projectAbs, p.id))
				} else {
					command = "error"
					args = []string{url}
				}
			} else {
				command = "echo"
				args = []string{"skipping package"}
			}
		case SCANNING:
			if request.index < len(p.scanners) {
				s := p.scanners[request.index]
				command = "bash"
				args = []string{"scan.sh", fmt.Sprintf("package-%d", p.id)}
				dir = fmt.Sprintf("%s/%d/workspace/source", projectAbs, s.id)
				env = []string{
					fmt.Sprintf("RACS_SCAN=%s", fmt.Sprintf("package-%d", p.id)),
					fmt.Sprintf("RACS_VERSION=%d", p.version),
					fmt.Sprintf("RACS_SCAN_URL=%s", p.url),
					fmt.Sprintf("RACS_SCAN_BRANCH=%s", p.branch),
					fmt.Sprintf("RACS_SCAN_COMMIT=%s", p.commit),
					fmt.Sprintf("RACS_SCAN_PROJECT=%d", p.id),
				}
				for name, cr := range s.credentials {
					env = append(env, fmt.Sprintf("%s=%s", name, credentialValue(cr)))
				}
			} else {
				command = "echo"
				args = []string{"skipping scan"}
			}
		case PUSHING:
			if request.from == SCANNING {
				command = "echo"
				args = []string{"skipping push"}
			} else if request.index < len(p.destinations) {
				destination := p.destinations[request.index]
				ok, url := registryLogin(destination.registry)
				if ok {
					tag := strings.Replace(destination.tag, "$VERSION", strconv.Itoa(p.version), -1)
					command = "podman"
					args = []string{"push", fmt.Sprintf("package-%d", p.id), fmt.Sprintf("%s/%s", url, tag)}
				} else {
					command = "error"
					args = []string{url}
				}
			} else {
				command = "echo"
				args = []string{"skipping push"}
			}
		case TAGGING:
			if request.from == SCANNING {
				command = "echo"
				args = []string{"skipping tag"}
			} else if p.tag != "" {
				tag := strings.Replace(p.tag, "$VERSION", strconv.Itoa(p.version), -1)
				tag = tag[strings.LastIndex(tag, ":")+1:]
				command = "git"
				args = []string{"-C", fmt.Sprintf("%s/%d/workspace/source", projectAbs, p.id), "push", "origin", tag}
			} else {
				command = "echo"
				args = []string{"skipping tag"}
			}
		case DELETING:
			command = "rm"
			args = []string{"-vrf", fmt.Sprintf("%s/%d", projectAbs, p.id)}
		}
		p.state = state
		if len(command) > 0 {
			var id int
			now := time.Now()
			err := db.QueryRow(`INSERT INTO tasks(project, type, state, time)
				VALUES(?, ?, 'QUEUED', ?) RETURNING id`, p.id, p.state.String(), now.Unix()).Scan(&id)
			if err != nil {
				logger.Fatal(err)
			}
			logger.Infof("Creating task %d:%d", p.id, id)
			t := &task{id, p.state, "QUEUED", now}
			p.tasks = append(p.tasks, t)
			if len(p.tasks) > 10 {
				p.tasks = p.tasks[1:]
			}
			event(map[string]interface{}{
				"event":   "task/create",
				"project": p.id,
				"id":      t.id,
				"type":    t.kind.String(),
				"time":    t.time.Unix(),
				"state":   "QUEUED",
			})
			ctx := context.TODO()
			jobSemaphore.Acquire(ctx, 1)
			t.state = "RUNNING"
			db.Exec(`UPDATE tasks SET state = ? WHERE id = ?`, t.state, t.id)
			event(map[string]interface{}{
				"event":   "task/state",
				"project": p.id,
				"id":      t.id,
				"state":   "RUNNING",
			})
			taskRoot := fmt.Sprintf("tasks/%d", t.id)
			os.Mkdir(taskRoot, 0777)
			logger.Infof("Task %s %v", command, args)
			out, _ := os.Create(fmt.Sprintf("%s/out.log", taskRoot))
			if command != "error" {
				cmd := exec.Command(command, args...)
				activeCommands[id] = cmd
				cmd.Dir = dir
				cmd.Env = append(cmd.Environ(), env...)
				out.WriteString("\u001B[1m")
				out.WriteString(cmd.String())
				out.WriteString("\u001B[0m\n")
				cmd.Stdout = out
				cmd.Stderr = out
				err = cmd.Run()
				jobSemaphore.Release(1)
				if err != nil {
					if err.Error() == "signal: killed" {
						projectStateMutex.Lock()
						t.state = "STOPPED"
						projectStateMutex.Unlock()
					} else {
						projectStateMutex.Lock()
						t.state = "ERROR"
						projectStateMutex.Unlock()
					}
					p.state += 1
				} else {
					projectStateMutex.Lock()
					t.state = "SUCCESS"
					projectStateMutex.Unlock()
					p.state += 2
				}
			} else {
				jobSemaphore.Release(1)
				out.WriteString(args[0])
				projectStateMutex.Lock()
				t.state = "ERROR"
				projectStateMutex.Unlock()
				p.state += 1
			}
			projectStateCond.Broadcast()
			out.Close()
			delete(activeCommands, t.id)
			logger.Infof("Task %d completed", t.id)
			db.Exec(`UPDATE projects SET state = ? WHERE id = ?`, p.state.String(), p.id)
			db.Exec(`UPDATE tasks SET state = ? WHERE id = ?`, t.state, t.id)
			event(map[string]interface{}{
				"event": "project/state",
				"id":    p.id,
				"state": p.state.String(),
			})
			event(map[string]interface{}{
				"event":   "task/state",
				"project": p.id,
				"id":      t.id,
				"state":   t.state,
			})
		}
		logger.Infof("Project %d finished task %s", p.id, state.String())
		switch p.state {
		case CREATE_SUCCESS:
			p.buildHash = []byte{}
			db.Exec(`UPDATE projects SET buildHash = ? WHERE id = ?`, p.buildHash, p.id)
			request = taskRequest{CLEANING, request.from, request.trigger, 0, false}
		case CLEAN_SUCCESS:
			request = taskRequest{CLONING, request.from, request.trigger, 0, false}
		case CLONE_SUCCESS:
			request = taskRequest{PREPARING, request.from, request.trigger, 0, false}
		case PREPARE_SUCCESS:
			request = taskRequest{PULLING, request.from, request.trigger, 0, false}
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
				db.Exec(`UPDATE projects SET buildHash = ? WHERE id = ?`, p.buildHash, p.id)
				request = taskRequest{PREPARING, request.from, request.trigger, 0, false}
			} else {
				if !p.protected || request.trigger == nil {
					request = taskRequest{BUILDING, request.from, request.trigger, 0, false}
				} else {
					request = <-p.queue
				}
			}
		case BUILD_SUCCESS:
			request = taskRequest{PREPACKAGING, request.from, request.trigger, 0, false}
		case PREPACKAGE_SUCCESS:
			request = taskRequest{PACKAGING, request.from, request.trigger, 0, false}
		case PACKAGE_SUCCESS:
			out, err := exec.Command("git", "-C", fmt.Sprintf("%s/%d/workspace/source", projectAbs, p.id), "rev-parse", "HEAD").Output()
			if err == nil {
				p.commit = strings.TrimSpace(string(out))
			}
			p.version += 1
			db.Exec(`UPDATE projects SET version = ? WHERE id = ?`, p.version, p.id)
			event(map[string]interface{}{
				"event":   "project/version",
				"id":      p.id,
				"version": p.version,
			})

			tags := make(map[string]int)
			for _, destination := range p.destinations {
				tag := strings.Replace(destination.tag, "$VERSION", strconv.Itoa(p.version), -1)
				tag = tag[strings.LastIndex(tag, ":")+1:]
				tags[tag] = 1
			}
			for tag, _ := range tags {
				_, err = exec.Command("git", "-C", fmt.Sprintf("%s/%d/workspace/source", projectAbs, p.id), "tag", tag).Output()
				if err != nil {
					logger.Error(err)
				}
			}
			request = taskRequest{SCANNING, request.from, request.trigger, 0, false}
		case SCAN_SUCCESS:
			index := request.index + 1
			if index < len(p.scanners) {
				request = taskRequest{SCANNING, request.from, request.trigger, index, false}
			} else {
				request = taskRequest{PUSHING, request.from, request.trigger, 0, false}
			}
		case PUSH_SUCCESS:
			index := request.index
			if (request.from != SCANNING || request.force) && len(p.triggers) > 0 {
				tag := ""
				registry := ""
				if index < len(p.destinations) {
					destination := p.destinations[index]
					tag = strings.Replace(destination.tag, "$VERSION", strconv.Itoa(p.version), -1)
					registry = destination.registry.name
				}
				taskTrigger := map[string]string{
					"URL":      p.url,
					"BRANCH":   p.branch,
					"COMMIT":   p.commit,
					"TAG":      tag,
					"REGISTRY": registry,
					"PROJECT":  strconv.Itoa(p.id),
					"VERSION":  strconv.Itoa(p.version),
				}
				//&taskTrigger{p.url, p.branch, p.commit, tag, registry, p.id, p.version}
				for target, trigger := range p.triggers {
					target.buildFrom(trigger.from, taskTrigger, false)
				}
			}
			request = taskRequest{TAGGING, request.state, request.trigger, index, false}
		case TAG_SUCCESS:
			index := request.index + 1
			if request.from != SCANNING && index < len(p.destinations) {
				request = taskRequest{PUSHING, request.state, request.trigger, index, false}
			} else {
				request = <-p.queue
			}
		case DELETE_SUCCESS:
			projectDelete(p)
			return
		default:
			request = <-p.queue
		}
	}
}

func projectCreate(name, url, branch, labels string) *project {
	var id int
	db.QueryRow(`INSERT INTO projects(name, source, branch, labels, buildSpec, prepackageSpec, packageSpec, state, version, protected)
		VALUES(?, ?, ?, ?, 'BuildSpec', '', 'PackageSpec', 'CLONING', 0, 0) RETURNING id`, name, url, branch, labels).Scan(&id)
	logger.Infof("Project created %s %s %s %s", id, name, url, branch)
	os.Mkdir(fmt.Sprintf("%s/%d", projectAbs, id), 0777)
	os.Mkdir(fmt.Sprintf("%s/%d/context", projectAbs, id), 0777)
	os.Mkdir(fmt.Sprintf("%s/%d/workspace", projectAbs, id), 0777)
	os.Mkdir(fmt.Sprintf("%s/%d/config", projectAbs, id), 0777)
	p := &project{
		id, name, labels, url, branch,
		"workspace/source/BuildSpec",
		"workspace/source/PrepackageSpec",
		"workspace/source/PackageSpec", []byte{},
		CREATE_SUCCESS, 0, false,
		make([]destination, 0),
		make(map[string]*registry),
		make([]*task, 0),
		make(chan taskRequest, 10),
		make(map[*project]trigger),
		make(map[string]*credential),
		nil, nil, nil, make([]*project, 0), "", "", "",
	}
	projects[p.id] = p
	go projectRoutine(p)
	event(map[string]interface{}{
		"event":          "project/create",
		"id":             p.id,
		"name":           p.name,
		"labels":         p.labels,
		"url":            p.url,
		"branch":         p.branch,
		"buildSpec":      p.buildSpec,
		"prepackageSpec": p.prepackageSpec,
		"packageSpec":    p.packageSpec,
		"state":          p.state.String(),
		"version":        p.version,
		"protected":      p.protected,
	})
	return p
}

func projectDelete(p *project) {
	for target, trigger := range p.triggers {
		for state := range trigger.states {
			switch state {
			case PREPARING:
				target.prepareDep = nil
			case PREPACKAGING:
				target.prepackageDep = nil
			case PACKAGING:
				target.packageDep = nil
			case SCANNING:
				scanners := target.scanners
				for n, q := range scanners {
					if p == q {
						target.scanners = append(scanners[:n], scanners[n+1:]...)
						break
					}
				}
			}
		}
	}
	rows, err := db.Query(`UPDATE credentials SET project = 0 WHERE project = ? RETURNING id`, p.id)
	if err == nil {
		for rows.Next() {
			var id int
			rows.Scan(&id)
			cr := credentials[id]
			if cr != nil {
				cr.project = 0
			}
		}
	}
	db.Exec(`DELETE FROM projects WHERE id = ?`, p.id)
	db.Exec(`DELETE FROM tasks WHERE project = ?`, p.id)
	db.Exec(`DELETE FROM triggers WHERE project = ?`, p.id)
	db.Exec(`DELETE FROM triggers WHERE target = ?`, p.id)
	db.Exec(`DELETE FROM destinations WHERE project = ?`, p.id)
	db.Exec(`DELETE FROM environments WHERE project = ?`, p.id)
	delete(projects, p.id)
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
		for _, t := range p.tasks {
			tasks = append(tasks, map[string]interface{}{
				"id":    t.id,
				"type":  t.kind.String(),
				"state": t.state,
				"time":  t.time.Unix(),
			})
		}
		destinations := make([]interface{}, 0)
		for _, destination := range p.destinations {
			destinations = append(destinations, []interface{}{
				destination.registry.id, destination.tag,
			})
		}
		sources := make(map[string]interface{}, 0)
		for stage, registry := range p.sources {
			sources[stage] = registry.id
		}
		triggers := make([]interface{}, 0)
		for target, trigger := range p.triggers {
			for state := range trigger.states {
				triggers = append(triggers, []interface{}{target.id, state.String()})
			}
		}
		environment := make([]interface{}, 0)
		for name, credential := range p.credentials {
			environment = append(environment, []interface{}{
				name, credential.id, credential.name,
			})
		}
		result = append(result, map[string]interface{}{
			"id":             id,
			"name":           p.name,
			"labels":         p.labels,
			"url":            p.url,
			"branch":         p.branch,
			"destinations":   destinations,
			"sources":        sources,
			"buildSpec":      p.buildSpec,
			"prepackageSpec": p.prepackageSpec,
			"packageSpec":    p.packageSpec,
			"state":          p.state.String(),
			"tasks":          tasks,
			"version":        p.version,
			"protected":      p.protected,
			"triggers":       triggers,
			"environment":    environment,
			"tag":            p.tag,
			"group":          p.group,
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

type sso_config struct {
	Login_url     string
	Server_url    string
	Client_id     string
	Client_secret string
	Scopes        string
	Users         map[string]string
}

var sso sso_config
var use_sso bool = false

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
		"action":  path,
		"params":  sb.String(),
		"use_sso": use_sso,
		"sso_url": sso.Login_url + "?response_type=code&scopes=" + url.QueryEscape(sso.Scopes) + "&client_id=" + url.QueryEscape(sso.Client_id),
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

func handleLogin(w http.ResponseWriter, r *http.Request, u *user, params map[string]string) {
	redirect := params["redirect"]
	renderLogin(w, "redirect", map[string]string{"redirect": redirect})
}

func handleEvents(w http.ResponseWriter, r *http.Request, u *user, params map[string]string) {
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
	ctx := r.Context()
	go func() {
		<-ctx.Done()
		clients.unregister <- events
	}()
	j, _ := json.Marshal(map[string]interface{}{
		"event": "user/current",
		"user":  u.Name,
	})
	fmt.Fprintf(w, "data: %s\n\n", j)
	j, _ = json.Marshal(map[string]interface{}{
		"event":    "project/list",
		"projects": projectList(),
	})
	fmt.Fprintf(w, "data: %s\n\n", j)
	j, _ = json.Marshal(map[string]interface{}{
		"event":       "credential/list",
		"credentials": credentialList(),
	})
	fmt.Fprintf(w, "data: %s\n\n", j)
	j, _ = json.Marshal(map[string]interface{}{
		"event":      "registry/list",
		"registries": registryList(),
	})
	fmt.Fprintf(w, "data: %s\n\n", j)
	flusher.Flush()
	for {
		fmt.Fprintf(w, "data: %s\n\n", <-events)
		flusher.Flush()
	}
}

func handleUserLogin(w http.ResponseWriter, r *http.Request, u *user, params map[string]string) {
	username := params["username"]
	password := params["password"]
	sso_code := params["sso_code"]
	if use_sso && len(sso_code) > 0 {
		command := "./sso_login.sh"
		args := []string{}
		env := []string{
			fmt.Sprintf("SSO_CODE=%s", sso_code),
			fmt.Sprintf("SERVER_URL=%s", sso.Server_url),
			fmt.Sprintf("CLIENT_ID=%s", sso.Client_id),
			fmt.Sprintf("CLIENT_SECRET=%s", sso.Client_secret),
		}
		cmd := exec.Command(command, args...)
		cmd.Env = append(cmd.Environ(), env...)
		username0, err := cmd.Output()
		if err != nil {
			logger.Error(err)
			w.WriteHeader(401)
			w.Write([]byte(err.Error()))
			return
		}
		username = strings.TrimSpace(string(username0))
		role := sso.Users[username]
		if len(role) == 0 {
			logger.Errorf("Unknown user %s", username)
			w.WriteHeader(401)
			w.Write([]byte(fmt.Sprintf("Unknown user %s", username)))
			return
		}
	} else {
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
		Expires: time.Now().Add(28 * time.Hour),
	}
	http.SetCookie(w, &cookie)
	action := params["action"]
	if len(action) > 0 {
		query, _ := url.ParseQuery(params["params"])
		params := make(map[string]string)
		for name, values := range query {
			params[name] = values[0]
		}
		if action == "redirect" {
			w.Header().Add("Location", params["redirect"])
			w.WriteHeader(303)
		} else {
			handleAction(action, w, r, &u2, params)
		}
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

var gv *graphviz.Graphviz

func handleProjectGraph(w http.ResponseWriter, r *http.Request, u *user, params map[string]string) {
	graph, _ := gv.Graph(graphviz.Directed)
	graph.SetRankDir("LR")
	graph.SetSplines("polyline")
	//graph.SetConcentrate(true)
	graph.SetRankSeparator(3)
	graph.SetOverlap(false)
	pnodes := make(map[int]*cgraph.Node)
	crnodes := make(map[int]*cgraph.Node)
	rnodes := make(map[int]*cgraph.Node)
	for _, p := range projects {
		node, _ := graph.CreateNode(fmt.Sprintf("P%d", p.id))
		node.SetLabel(fmt.Sprintf("#%d %s", p.id, p.name))
		node.SetStyle("filled")
		node.SetShape("component")
		node.SetFillColor("#ff440022")
		pnodes[p.id] = node
	}
	for _, cr := range credentials {
		node, _ := graph.CreateNode(fmt.Sprintf("CR%d", cr.id))
		node.SetLabel(cr.name)
		node.SetStyle("filled")
		node.SetShape("signature")
		node.SetFillColor("#0044ff22")
		crnodes[cr.id] = node
		if cr.project > 0 {
			tnode := pnodes[cr.project]
			graph.CreateEdge("", tnode, node)
		}
	}
	for _, r := range registries {
		node, _ := graph.CreateNode(fmt.Sprintf("R%d", r.id))
		node.SetLabel(r.name)
		node.SetStyle("filled")
		node.SetShape("cylinder")
		node.SetFillColor("#44ff0022")
		rnodes[r.id] = node
		if r.credential > 0 {
			crnode := crnodes[r.credential]
			if crnode == nil {
				crnode, _ = graph.CreateNode(fmt.Sprintf("CR%d", r.credential))
			}
			graph.CreateEdge("", crnode, node)
		}
	}
	for _, p := range projects {
		pnode := pnodes[p.id]
		for q, t := range p.triggers {
			for s := range t.states {
				tnode := pnodes[q.id]
				edge, _ := graph.CreateEdge("", pnode, tnode)
				label := edge.Get("label")
				if label != "" {
					label = fmt.Sprintf("%s|%s", label, s.String())
				} else {
					label = s.String()
				}
				edge.SetLabel(label)
			}
		}
		for name, cr := range p.credentials {
			crnode := crnodes[cr.id]
			edge, _ := graph.CreateEdge("", crnode, pnode)
			edge.SetLabel(fmt.Sprintf("%s", name))
		}
		for _, d := range p.destinations {
			graph.CreateEdge("", pnode, rnodes[d.registry.id])
		}
		if p.buildSpec != "" {
			spec := fmt.Sprintf("%s/%d/%s", projectAbs, p.id, p.buildSpec)
			r := registryBySpec(spec)
			if r != nil {
				edge, _ := graph.CreateEdge("", rnodes[r.id], pnode)
				edge.SetLabel("Build")
			}
		}
		if p.prepackageSpec != "" {
			spec := fmt.Sprintf("%s/%d/%s", projectAbs, p.id, p.prepackageSpec)
			r := registryBySpec(spec)
			if r != nil {
				edge, _ := graph.CreateEdge("", rnodes[r.id], pnode)
				edge.SetLabel("Prepackage")
			}
		}
		if p.packageSpec != "" {
			spec := fmt.Sprintf("%s/%d/%s", projectAbs, p.id, p.packageSpec)
			r := registryBySpec(spec)
			if r != nil {
				edge, _ := graph.CreateEdge("", rnodes[r.id], pnode)
				edge.SetLabel("Package")
			}
		}
	}

	format := graphviz.SVG
	contentType := "image/svg+xml"

	switch params["format"] {
	case "xdot":
		format = graphviz.XDOT
		contentType = "text/plain"
	case "png":
		format = graphviz.PNG
		contentType = "image/png"
	case "jpg":
		format = graphviz.JPG
		contentType = "image/jpeg"
	default:
		format = graphviz.SVG
		contentType = "image/svg+xml"
	}

	var out bytes.Buffer
	if err := gv.Render(graph, format, &out); err != nil {
		logger.Error(err)
		w.WriteHeader(500)
		w.Write([]byte(err.Error()))
	} else {
		w.Header().Add("Content-Type", contentType)
		w.WriteHeader(200)
		w.Write(out.Bytes())
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
			"id":     id,
			"name":   p.name,
			"url":    p.url,
			"branch": p.branch,
			//"destination":    p.destination,
			"buildSpec":      p.buildSpec,
			"prepackageSpec": p.prepackageSpec,
			"packageSpec":    p.packageSpec,
			//"tag":            p.tag,
			"labels": p.labels,
		})
		w.Write(j)
	}
}

func projectUpdateEvent(p *project) {
	destinations := make([]interface{}, 0)
	for _, destination := range p.destinations {
		destinations = append(destinations, []interface{}{
			destination.registry.id, destination.tag,
		})
	}

	sources := make(map[string]interface{}, 0)
	for stage, registry := range p.sources {
		sources[stage] = registry.id
	}
	triggers := make([]interface{}, 0)
	for target, trigger := range p.triggers {
		for state := range trigger.states {
			triggers = append(triggers, []interface{}{target.id, state.String()})
		}
	}
	environment := make([]interface{}, 0)
	for name, credential := range p.credentials {
		environment = append(environment, []interface{}{
			name, credential.id, credential.name,
		})
	}
	event(map[string]interface{}{
		"event":          "project/update",
		"id":             p.id,
		"name":           p.name,
		"labels":         p.labels,
		"url":            p.url,
		"branch":         p.branch,
		"destinations":   destinations,
		"sources":        sources,
		"buildSpec":      p.buildSpec,
		"prepackageSpec": p.prepackageSpec,
		"packageSpec":    p.packageSpec,
		"protected":      p.protected,
		"triggers":       triggers,
		"environment":    environment,
		"tag":            p.tag,
		"group":          p.group,
	})
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
		if params["buildSpec"] != "" {
			p.buildSpec = filepath.Clean(params["buildSpec"])
		} else {
			p.buildSpec = ""
		}
		if params["prepackageSpec"] != "" {
			p.prepackageSpec = filepath.Clean(params["prepackageSpec"])
		} else {
			p.prepackageSpec = ""
		}
		if params["packageSpec"] != "" {
			p.packageSpec = filepath.Clean(params["packageSpec"])
		} else {
			p.packageSpec = ""
		}
		p.tag = params["tag"]
		p.group = params["group"]
		p.protected = params["protected"] != ""
		db.Exec(`UPDATE projects SET name = ?, labels = ?, source = ?, branch = ?, buildSpec = ?, prepackageSpec = ?, packageSpec = ?, protected = ?, "group" = ? WHERE id = ?`,
			p.name, p.labels, p.url, p.branch, p.buildSpec, p.prepackageSpec, p.packageSpec, p.protected, p.group, p.id)
		projectUpdateEvent(p)
		exec.Command("git", "-C", fmt.Sprintf("%s/%d/workspace/source", projectAbs, p.id), "remote", "set-url", "origin", p.url).Output()
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
	labels := params["labels"]
	p := projectCreate(name, url, branch, labels)
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
	pid, _ := strconv.Atoi(params["id"])
	p := projects[pid]
	name := filepath.Clean(params["name"])
	upload := filepath.Clean(params["upload"])
	validUpload, _ := regexp.MatchString("^uploads/upload-[0-9]+$", upload)
	if p == nil {
		w.WriteHeader(500)
	} else if name == "." {
		w.WriteHeader(500)
	} else if !validUpload {
		w.WriteHeader(500)
	} else {
		err := os.Rename(upload, fmt.Sprintf("%s/%d/%s", projectAbs, p.id, name))
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

func handleProjectConfigList(w http.ResponseWriter, r *http.Request, u *user, params map[string]string) {
	if checkLogin(u, "admin", w, "/project/config", params) {
		return
	}
	pid, _ := strconv.Atoi(params["id"])
	p := projects[pid]
	files := make([]map[string]interface{}, 0)
	entries, _ := os.ReadDir(fmt.Sprintf("%s/%d/config", projectAbs, p.id))
	for _, e := range entries {
		if !e.IsDir() {
			info, _ := e.Info()
			files = append(files, map[string]interface{}{
				"name": e.Name(),
				"size": info.Size(),
				"time": info.ModTime().Unix(),
			})
		}
	}
	w.Header().Add("Content-Type", "application/json")
	j, _ := json.Marshal(files)
	w.Write(j)
}

func handleProjectConfigRead(w http.ResponseWriter, r *http.Request, u *user, params map[string]string) {
	if checkLogin(u, "admin", w, "/project/config", params) {
		return
	}
	pid, _ := strconv.Atoi(params["id"])
	p := projects[pid]
	name := filepath.Clean(params["name"])
	path := fmt.Sprintf("%s/%d/config/%s", projectAbs, p.id, name)
	logger.Infof("Reading config %s", path)
	text, err := ioutil.ReadFile(path)
	if err != nil {
		w.WriteHeader(404)
		w.Write([]byte(err.Error()))
	} else {
		w.Header().Add("Content-Type", "text/plain")
		w.Write(text)
	}
}

func handleProjectDestinations(w http.ResponseWriter, r *http.Request, u *user, params map[string]string) {
	if checkLogin(u, "admin", w, "/project/destinations", params) {
		return
	}
	pid, _ := strconv.Atoi(params["id"])
	p := projects[pid]
	p.destinations = make([]destination, 0)
	db.Exec(`DELETE FROM destinations WHERE project = ?`, p.id)
	destinations := strings.FieldsFunc(params["destinations"], func(c rune) bool {
		return c == ','
	})
	logger.Infof("Destinations = %s", destinations)
	for i := 0; i < len(destinations); i += 3 {
		rid, _ := strconv.Atoi(destinations[i])
		r := registries[rid]
		tag := destinations[i+1]
		p.destinations = append(p.destinations, destination{r, tag})
		db.Exec(`INSERT INTO destinations(project, registry, tag) VALUES(?, ?, ?)`, p.id, r.id, tag)
	}
	projectUpdateEvent(p)
	redirect := params["redirect"]
	if len(redirect) > 0 {
		w.Header().Add("Location", redirect)
		w.WriteHeader(303)
	} else {
		w.WriteHeader(200)
		w.Write([]byte("OK"))
	}
}

func handleProjectTriggers(w http.ResponseWriter, r *http.Request, u *user, params map[string]string) {
	if checkLogin(u, "admin", w, "/project/triggers", params) {
		return
	}
	pid, _ := strconv.Atoi(params["id"])
	p := projects[pid]
	for target, trigger := range p.triggers {
		for state := range trigger.states {
			switch state {
			case PREPARING:
				target.prepareDep = nil
			case PREPACKAGING:
				target.prepackageDep = nil
			case PACKAGING:
				target.packageDep = nil
			case SCANNING:
				scanners := target.scanners
				for n, q := range scanners {
					if p == q {
						target.scanners = append(scanners[:n], scanners[n+1:]...)
						break
					}
				}
			}
		}
	}
	p.triggers = make(map[*project]trigger, 0)
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
		case "prepackage":
			s = PREPACKAGING
		case "package":
			s = PACKAGING
		case "scan":
			s = SCANNING
		case "push":
			s = PUSHING
		case "tag":
			s = TAGGING
		}
		trigger, exists := p.triggers[t]
		if !exists {
			trigger.from = s
			trigger.states = make(map[state]bool, 0)
		}
		trigger.states[s] = true
		if s < trigger.from {
			trigger.from = s
		}
		p.triggers[t] = trigger
		switch s {
		case PREPARING:
			t.prepareDep = p
		case PREPACKAGING:
			t.prepackageDep = p
		case PACKAGING:
			t.packageDep = p
		case SCANNING:
			t.scanners = append(t.scanners, p)
		}
		db.Exec(`INSERT INTO triggers(project, target, state) VALUES(?, ?, ?)`, p.id, t.id, s.String())
	}
	projectUpdateEvent(p)
	redirect := params["redirect"]
	if len(redirect) > 0 {
		w.Header().Add("Location", redirect)
		w.WriteHeader(303)
	} else {
		w.WriteHeader(200)
		w.Write([]byte("OK"))
	}
}

func handleProjectEnvironment(w http.ResponseWriter, r *http.Request, u *user, params map[string]string) {
	if checkLogin(u, "admin", w, "/project/environment", params) {
		return
	}
	pid, _ := strconv.Atoi(params["id"])
	p := projects[pid]
	p.credentials = make(map[string]*credential)
	db.Exec(`DELETE FROM environments WHERE project = ?`, p.id)
	environment := strings.FieldsFunc(params["environment"], func(c rune) bool {
		return c == ','
	})
	for i := 0; i < len(environment); i += 2 {
		name := environment[i]
		crid, _ := strconv.Atoi(environment[i+1])
		cr := credentials[crid]
		if cr != nil {
			p.credentials[name] = cr
			db.Exec(`INSERT INTO environments(project, name, credential) VALUES(?, ?, ?)`, p.id, name, cr.id)
		}
	}
	projectUpdateEvent(p)
	redirect := params["redirect"]
	if len(redirect) > 0 {
		w.Header().Add("Location", redirect)
		w.WriteHeader(303)
	} else {
		w.WriteHeader(200)
		w.Write([]byte("OK"))
	}
}

func findProjects(ps []*project, ref string, repo map[string]interface{}) []*project {
	logger.Infof("Trying to match project %v, %v", ref, repo)
	for _, p := range projects {
		if p.url == repo["clone_url"] || p.url == repo["html_url"] || p.url == repo["ssh_url"] {
			if fmt.Sprintf("refs/heads/%s", p.branch) == ref {
				ps = append(ps, p)
			}
		}
	}
	return ps
}

func handleProjectBuild(w http.ResponseWriter, r *http.Request, u *user, params map[string]string) {
	var ps []*project
	if params["id"] != "" {
		id, _ := strconv.Atoi(params["id"])
		ps = append(ps, projects[id])
	} else if params["payload"] != "" {
		var j map[string]interface{}
		json.Unmarshal([]byte(params["payload"]), &j)
		repo := j["repository"].(map[string]interface{})
		ref := j["ref"].(string)
		ps = findProjects(ps, ref, repo)
	} else if params["repository"] != "" {
		var repo map[string]interface{}
		json.Unmarshal([]byte(params["repository"]), &repo)
		ref := params["ref"]
		ps = findProjects(ps, ref, repo)
	}
	if len(ps) == 0 {
		w.WriteHeader(400)
		w.Write([]byte("Invalid project"))
		return
	}
	stage := params["stage"]
	requestedRef := ""
	if params["payload"] != "" {
		var j map[string]interface{}
		json.Unmarshal([]byte(params["payload"]), &j)
		requestedRef = fmt.Sprint(j["ref"])
	} else if params["ref"] != "" {
		requestedRef = params["ref"]
	}
	for _, p := range ps {
		expectedRef := fmt.Sprintf("refs/heads/%s", p.branch)
		if requestedRef == expectedRef || requestedRef == "" {
			if p.protected && u.Name == "" {
				w.WriteHeader(403)
				w.Write([]byte("Unauthorized"))
				return
			}
			switch stage {
			case "clean":
				p.buildFrom(CLEANING, nil, true)
			case "clone":
				p.buildFrom(CLONING, nil, true)
			case "prepare":
				p.buildFrom(PREPARING, nil, true)
			case "pull":
				p.buildFrom(PULLING, nil, true)
			case "build":
				p.buildFrom(BUILDING, nil, true)
			case "prepackage":
				p.buildFrom(PREPACKAGING, nil, true)
			case "package":
				p.buildFrom(PACKAGING, nil, true)
			case "scan":
				p.buildFrom(SCANNING, nil, true)
			case "push":
				p.buildFrom(PUSHING, nil, true)
			case "tag":
				p.buildFrom(TAGGING, nil, true)
			}
		} else {
			logger.Infof("Build requested by %s expected %s, skipping", requestedRef, expectedRef)
		}
	}
	w.WriteHeader(200)
	w.Write([]byte("OK"))
}

func handleTaskStop(w http.ResponseWriter, r *http.Request, u *user, params map[string]string) {
	if checkLogin(u, "admin", w, "/task/stop", params) {
		return
	}
	if params["id"] == "" {
		w.WriteHeader(500)
		w.Write([]byte("Task Id is required"))
	} else {
		id, _ := strconv.Atoi(params["id"])
		if cmd := activeCommands[id]; cmd != nil {
			if err := cmd.Process.Kill(); err != nil {
				logger.Warnf("Unable to stop task %d", id)
				w.WriteHeader(501)
				w.Write([]byte("Unable to stop task command"))
			} else {
				w.WriteHeader(200)
				w.Write([]byte("OK"))
			}
		} else {
			w.WriteHeader(200)
			w.Write([]byte("OK"))
		}
	}
}

func handleProjectDelete(w http.ResponseWriter, r *http.Request, u *user, params map[string]string) {
	if checkLogin(u, "admin", w, "/project/delete", params) {
		return
	}
	id, _ := strconv.Atoi(params["id"])
	confirm := params["confirm"]
	if confirm == "YES" {
		projects[id].buildFrom(DELETING, nil, true)
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

func handleTaskList(w http.ResponseWriter, r *http.Request, u *user, params map[string]string) {
	from, _ := strconv.ParseInt(params["from"], 10, 64)
	result := make([]interface{}, 0)
	if params["id"] != "" {
		pid, _ := strconv.Atoi(params["id"])
		rows, _ := db.Query(`SELECT id, type, state, time FROM tasks WHERE project = ? ORDER BY id DESC LIMIT 100 OFFSET ?`, pid, from)
		for rows.Next() {
			var id int
			var kind string
			var state string
			var time int64
			rows.Scan(&id, &kind, &state, &time)
			result = append(result, map[string]interface{}{
				"id":    id,
				"type":  kind,
				"state": state,
				"time":  time,
			})
		}
	} else {
		rows, _ := db.Query(`SELECT project, id, type, state, time FROM tasks ORDER BY id DESC LIMIT 100 OFFSET ?`, from)
		for rows.Next() {
			var pid int
			var id int
			var kind string
			var state string
			var time int64
			rows.Scan(&pid, &id, &kind, &state, &time)
			result = append(result, map[string]interface{}{
				"project": pid,
				"id":      id,
				"type":    kind,
				"state":   state,
				"time":    time,
			})
		}
	}
	w.Header().Add("Content-Type", "application/json")
	j, _ := json.Marshal(result)
	w.Write(j)
}

var loginToSeeLogs = []byte("Log in to see logs")

func handleTaskLogs(w http.ResponseWriter, r *http.Request, u *user, params map[string]string) {
	showLogs := false
	for _, r := range u.Roles {
		if r == "admin" {
			showLogs = true
		}
	}
	id, _ := strconv.Atoi(params["id"])
	offset, _ := strconv.ParseInt(params["offset"], 10, 64)
	var state string
	db.QueryRow(`SELECT state FROM tasks WHERE id = ?`, id).Scan(&state)
	if showLogs {
		file, _ := os.Open(fmt.Sprintf("tasks/%d/out.log", id))
		file.Seek(offset, 0)
		bytes, _ := ioutil.ReadAll(file)
		w.Header().Add("Content-Type", "text/plain")
		w.Header().Add("X-Task-State", state)
		w.Write(bytes)
	} else {
		w.Header().Add("Content-Type", "text/plain")
		w.Header().Add("X-Task-State", state)
		w.Write(loginToSeeLogs[offset:])
	}
}

func handleRegistryList(w http.ResponseWriter, r *http.Request, u *user, params map[string]string) {
	result := registryList()
	w.Header().Add("Content-Type", "application/json")
	j, _ := json.Marshal(result)
	w.Write(j)
}

func handleRegistryCreate(w http.ResponseWriter, r *http.Request, u *user, params map[string]string) {
	if checkLogin(u, "admin", w, "/registry/create", params) {
		return
	}
	name := params["name"]
	url := params["url"]
	user := params["user"]
	credential, _ := strconv.Atoi(params["credential"])
	timeout, _ := strconv.Atoi(params["timeout"])
	reg := registryCreate(name, url, user, credential, timeout)
	redirect := params["redirect"]
	if len(redirect) > 0 {
		w.Header().Add("Location", redirect)
		w.WriteHeader(303)
	} else {
		w.WriteHeader(201)
		w.Write([]byte(reg.name))
	}
}

func handleRegistryUpdate(w http.ResponseWriter, r *http.Request, u *user, params map[string]string) {
	if checkLogin(u, "admin", w, "/registry/update", params) {
		return
	}
	id, _ := strconv.Atoi(params["id"])
	reg := registries[id]
	reg.name = params["name"]
	reg.url = params["url"]
	reg.user = params["user"]
	reg.credential, _ = strconv.Atoi(params["credential"])
	reg.timeout, _ = strconv.Atoi(params["timeout"])
	db.Exec(`UPDATE registries SET name = ?, url = ?, user = ?, credential = ?, timeout = ? WHERE id = ?`, reg.name, reg.url, reg.user, reg.credential, reg.timeout, reg.id)
	redirect := params["redirect"]
	if len(redirect) > 0 {
		w.Header().Add("Location", redirect)
		w.WriteHeader(303)
	} else {
		w.WriteHeader(201)
		w.Write([]byte(reg.name))
	}
}

func handleRegistryDelete(w http.ResponseWriter, r *http.Request, u *user, params map[string]string) {
	if checkLogin(u, "admin", w, "/registry/delete", params) {
		return
	}
	id, _ := strconv.Atoi(params["id"])
	registry := registries[id]
	confirm := params["confirm"]
	if confirm == "YES" {
		rows, err := db.Query(`DELETE FROM destinations WHERE registry = ? RETURNING project`, id)
		if err == nil {
			for rows.Next() {
				var id int
				rows.Scan(&id)
				p := projects[id]
				if p != nil {
					p.destinations = slices.DeleteFunc(p.destinations, func(d destination) bool {
						return d.registry == registry
					})
					projectUpdateEvent(p)
				}
			}
		}
		db.Exec(`DELETE FROM registries WHERE id = ?`, id)
		delete(registries, id)
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

func credentialList() []map[string]interface{} {
	result := make([]map[string]interface{}, 0)
	for id, cr := range credentials {
		result = append(result, map[string]interface{}{
			"id":          id,
			"name":        cr.name,
			"project":     cr.project,
			"request":     cr.request,
			"expiry":      cr.expiry.Unix(),
			"updated":     cr.updated.Unix(),
			"description": cr.description,
		})
	}
	sort.Slice(result, func(i, j int) bool {
		adesc := result[i]["name"].(string)
		bdesc := result[j]["name"].(string)
		return adesc < bdesc
	})
	return result
}

func handleCredentialList(w http.ResponseWriter, r *http.Request, u *user, params map[string]string) {
	w.Header().Add("Content-Type", "application/json")
	j, _ := json.Marshal(credentialList())
	w.Write(j)
}

var credentialCiph cipher.Block

func credentialEncrypt(value string) string {
	if value == "" {
		return ""
	}
	gcm, _ := cipher.NewGCM(credentialCiph)
	nonceSize := gcm.NonceSize()
	nonce := make([]byte, nonceSize)
	rand.Read(nonce)
	en := gcm.Seal(nil, nonce, []byte(value), nil)
	out := make([]byte, len(en)+nonceSize)
	copy(out[:nonceSize], nonce)
	copy(out[nonceSize:], en)
	return hex.EncodeToString(out)
}

func credentialDecrypt(value string) string {
	if value == "" {
		return ""
	}
	gcm, _ := cipher.NewGCM(credentialCiph)
	nonceSize := gcm.NonceSize()
	en, _ := hex.DecodeString(value)
	nonce, in := en[:nonceSize], en[nonceSize:]
	de, _ := gcm.Open(nil, nonce, in, nil)
	return string(de)
}

func handleCredentialCreate(w http.ResponseWriter, r *http.Request, u *user, params map[string]string) {
	if checkLogin(u, "admin", w, "/credential/create", params) {
		return
	}
	name := params["name"]
	value := params["value"]
	project, _ := strconv.Atoi(params["project"])
	request := params["request"]
	description := params["description"]
	var id int
	now := time.Now()
	db.QueryRow(`INSERT INTO credentials(name, value, project, request, updated, description) VALUES(?, ?, ?, ?, ?, ?) RETURNING id`, name, credentialEncrypt(value), project, request, now.Unix(), description).Scan(&id)
	credentials[id] = &credential{id, name, value, project, request, time.Unix(0, 0), now, description}
	redirect := params["redirect"]
	if len(redirect) > 0 {
		w.Header().Add("Location", redirect)
		w.WriteHeader(303)
	} else {
		w.WriteHeader(201)
		w.Write([]byte(strconv.Itoa(id)))
	}
}

func handleCredentialUpdate(w http.ResponseWriter, r *http.Request, u *user, params map[string]string) {
	if checkLogin(u, "admin", w, "/credential/update", params) {
		return
	}
	id, _ := strconv.Atoi(params["id"])
	name := params["name"]
	value := params["value"]
	project, _ := strconv.Atoi(params["project"])
	request := params["request"]
	description := params["description"]
	cr := credentials[id]
	cr.name = name
	cr.description = description
	cr.project = project
	cr.request = request
	if cr.value != value {
		cr.value = value
		cr.updated = time.Now()
		db.Exec(`UPDATE credentials SET name = ?, value = ?, project = ?, request = ?, updated = ?, description = ? WHERE id = ?`, name, credentialEncrypt(value), project, request, cr.updated.Unix(), description, id)
	} else {
		db.Exec(`UPDATE credentials SET name = ?, project = ?, request = ?, description = ? WHERE id = ?`, name, project, request, description, id)
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

func handleCredentialDelete(w http.ResponseWriter, r *http.Request, u *user, params map[string]string) {
	if checkLogin(u, "admin", w, "/credential/delete", params) {
		return
	}
	id, _ := strconv.Atoi(params["id"])
	confirm := params["confirm"]
	if confirm == "YES" {
		rows, err := db.Query(`DELETE FROM environments WHERE credential = ? RETURNING project, name`, id)
		if err == nil {
			for rows.Next() {
				var id int
				var name string
				rows.Scan(&id, &name)
				p := projects[id]
				if p != nil {
					delete(p.credentials, name)
					projectUpdateEvent(p)
				}
			}
		}
		rows, err = db.Query(`UPDATE registries SET credential = 0 WHERE credential = ? RETURNING id`, id)
		if err == nil {
			for rows.Next() {
				var id int
				rows.Scan(&id)
				r := registries[id]
				if r != nil {
					r.credential = 0
				}
			}
		}
		db.Exec(`DELETE FROM credentials WHERE id = ?`, id)
		delete(credentials, id)
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

type handler func(w http.ResponseWriter, r *http.Request, u *user, params map[string]string)

var handlers = map[string]handler{}

func handleAction(path string, w http.ResponseWriter, r *http.Request, u *user, params map[string]string) bool {
	handler := handlers[path]
	if handler != nil {
		handler(w, r, u, params)
		return true
	} else {
		return false
	}
}

var templates *template.Template

func handleRoot(w http.ResponseWriter, r *http.Request) {
	path := r.URL.Path
	logger.Infof("%s %s %s", r.Method, r.RemoteAddr, path)
	contentType := r.Header.Get("Content-Type")
	params := make(map[string]string)
	for name, value := range r.URL.Query() {
		params[name] = value[0]
	}
	if strings.HasPrefix(contentType, "application/json") {
		body, _ := ioutil.ReadAll(r.Body)
		var j map[string]interface{}
		json.Unmarshal(body, &j)
		for name, value := range j {
			switch v := value.(type) {
			case string:
				params[name] = v
			default:
				j, _ := json.Marshal(v)
				params[name] = string(j)
			}
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
		u.Roles = append(u.Roles, "user")
		u.Roles = append(u.Roles, "admin")
	}
	cookie, _ := r.Cookie("RACS_TOKEN")
	if cookie != nil {
		b, _ := hex.DecodeString(cookie.Value)
		gcm, _ := cipher.NewGCM(ciph)
		nonceSize := gcm.NonceSize()
		nonce, in := b[:nonceSize], b[nonceSize:]
		de, _ := gcm.Open(nil, nonce, in, nil)
		json.Unmarshal(de, &u)
	}
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
	if template := templates.Lookup(path[1:]); template != nil {
		w.Header().Add("Content-Type", contentType)
		template.Execute(w, nil)
	} else if content, err := loadStatic(path); err == nil {
		w.Header().Add("Content-Type", contentType)
		w.Write(content)
	} else {
		w.WriteHeader(404)
		w.Write([]byte("Not found"))
	}
}

func main() {
	var sslCert, sslKey string
	var port int
	var limit int64
	var ssoConfig string
	flag.StringVar(&sslCert, "ssl-cert", "", "SSL cert")
	flag.StringVar(&sslKey, "ssl-key", "", "SSL key")
	flag.BoolVar(&noLogin, "no-login", false, "Allow all actions without login")
	flag.IntVar(&port, "port", 8080, "Web server port")
	flag.Int64Var(&limit, "limit", 8, "Job limit")
	flag.StringVar(&ssoConfig, "sso-config", "", "SSO config file")
	flag.Parse()

	if len(ssoConfig) > 0 {
		content, err := ioutil.ReadFile(ssoConfig)
		if err != nil {
			logger.Fatal("Error when opening file: ", err)
		}
		err = json.Unmarshal(content, &sso)
		if err != nil {
			logger.Fatal("Error when opening file: ", err)
		}
		use_sso = true
	}

	logger.Infof("Set job limit to %d", limit)

	gv = graphviz.New()
	key := make([]byte, 32)
	rand.Read(key)
	ciph, _ = aes.NewCipher(key)
	jobSemaphore = semaphore.NewWeighted(limit)

	var err error

	os.Mkdir("projects", 0777)
	os.Mkdir("tasks", 0777)
	os.Mkdir("uploads", 0777)
	os.Setenv("GIT_TERMINAL_PROMPT", "0")

	db, err = sql.Open("sqlite3", "file:main.db?cache=shared")
	if err != nil {
		logger.Fatal(err)
		os.Exit(-1)
	}
	defer db.Close()
	db.SetMaxOpenConns(1)

	var version int
	err = db.QueryRow(`SELECT value FROM config WHERE name = 'version'`).Scan(&version)
	if err != nil {
		bytes, _ := ioutil.ReadFile("schemas/current.sql")
		stats := strings.Split(string(bytes), ";")
		for _, stat := range stats {
			_, err := db.Exec(stat)
			if err != nil {
				logger.Fatal(err)
				os.Exit(-1)
			}
		}
	} else {
		for {
			bytes, err := ioutil.ReadFile(fmt.Sprintf("schemas/upgrade-%d.sql", version))
			if err != nil {
				break
			}
			stats := strings.Split(string(bytes), ";")
			for _, stat := range stats {
				stat = strings.TrimSpace(stat)
				if len(stat) > 0 {
					logger.Infof("Executing upgrade SQL: %s", stat)
					_, err := db.Exec(stat)
					if err != nil {
						logger.Fatal(err)
						os.Exit(-1)
					}
				}
			}
			version += 1
			db.Exec(`UPDATE config SET value = ? WHERE name = 'version'`, version)
		}
	}

	var credentialKey []byte
	err = db.QueryRow(`SELECT value FROM config WHERE name = 'key'`).Scan(&credentialKey)
	if err == sql.ErrNoRows {
		credentialKey := make([]byte, 32)
		rand.Read(credentialKey)
		credentialCiph, _ = aes.NewCipher(credentialKey)
		db.Exec(`INSERT INTO config VALUES('key', ?)`, credentialKey)
		rows, _ := db.Query(`SELECT id, value FROM credentials`)
		updates := make(map[int]string, 0)
		for rows.Next() {
			var id int
			var value string
			rows.Scan(&id, &value)
			updates[id] = credentialEncrypt(value)
		}
		for id, enc := range updates {
			db.Exec(`UPDATE credentials SET value = ? WHERE id = ?`, enc, id)
		}
	} else {
		credentialCiph, _ = aes.NewCipher(credentialKey)
	}

	states := make(map[string]state)
	for state := DELETING; state <= TAG_SUCCESS; state += 1 {
		states[state.String()] = state
	}
	db.Exec(`UPDATE tasks SET state = 'STOPPED' WHERE state = 'RUNNING'`)
	rows, err := db.Query(`SELECT id, name, url, user, credential, timeout FROM registries`)
	for rows.Next() {
		var id int
		var name string
		var url string
		var user string
		var credential int
		var timeout int
		rows.Scan(&id, &name, &url, &user, &credential, &timeout)
		registries[id] = &registry{id, name, url, user, credential, time.Unix(0, 0), timeout}
	}
	rows, err = db.Query(`SELECT id, name, description, value, project, request, expiry, updated FROM credentials`)
	for rows.Next() {
		var id int
		var name string
		var description string
		var value string
		var project int
		var request string
		var expiry int64
		var updated int64
		rows.Scan(&id, &name, &description, &value, &project, &request, &expiry, &updated)
		logger.Infof("Loading credential: %d: %s -> %s, %d", id, name, description, updated)
		cr := &credential{id, name, credentialDecrypt(value), project, request, time.Unix(expiry, 0), time.Unix(updated, 0), description}
		credentials[cr.id] = cr
	}
	rows, err = db.Query(`SELECT id, name, labels, source, branch, buildSpec, prepackageSpec, packageSpec, buildHash, state, version, protected, tag, "group" FROM projects`)
	for rows.Next() {
		var id int
		var name string
		var source string
		var branch string
		var buildSpec string
		var prepackageSpec string
		var packageSpec string
		var buildHash []byte
		var labels string
		var state string
		var version int
		var protected int
		var tag string
		var group string
		err := rows.Scan(&id, &name, &labels, &source, &branch, &buildSpec, &prepackageSpec, &packageSpec, &buildHash, &state, &version, &protected, &tag, &group)
		if err != nil {
			logger.Error(err)
		}
		p := &project{
			id, name, labels, source, branch, buildSpec, prepackageSpec, packageSpec, buildHash,
			states[state], version, protected == 1,
			make([]destination, 0),
			make(map[string]*registry),
			make([]*task, 0),
			make(chan taskRequest, 10),
			make(map[*project]trigger),
			make(map[string]*credential),
			nil, nil, nil, make([]*project, 0), "", tag, group,
		}
		out, err := exec.Command("git", "-C", fmt.Sprintf("%s/%d/workspace/source", projectAbs, p.id), "rev-parse", "HEAD").Output()
		if err == nil {
			p.commit = strings.TrimSpace(string(out))
		}
		if p.buildSpec != "" {
			spec := fmt.Sprintf("%s/%d/%s", projectAbs, p.id, p.buildSpec)
			r := registryBySpec(spec)
			if r != nil {
				p.sources["Build"] = r
			}
		}
		if p.prepackageSpec != "" {
			spec := fmt.Sprintf("%s/%d/%s", projectAbs, p.id, p.prepackageSpec)
			r := registryBySpec(spec)
			if r != nil {
				p.sources["Prepackage"] = r
			}
		}
		if p.packageSpec != "" {
			spec := fmt.Sprintf("%s/%d/%s", projectAbs, p.id, p.packageSpec)
			r := registryBySpec(spec)
			if r != nil {
				p.sources["Package"] = r
			}
		}
		//fmt.Printf("%+v\n", p)
		projects[p.id] = p
		go projectRoutine(p)
	}
	rows, err = db.Query(`SELECT project, registry, tag FROM destinations`)
	for rows.Next() {
		var pid int
		var rid int
		var tag string
		err := rows.Scan(&pid, &rid, &tag)
		if err != nil {
			logger.Error(err)
		}
		p := projects[pid]
		r := registries[rid]
		if p != nil && r != nil {
			p.destinations = append(p.destinations, destination{r, tag})
		}
	}
	rows, err = db.Query(`SELECT project, id, type, state, time FROM tasks ORDER BY id`)
	for rows.Next() {
		var pid int
		var id int
		var kind string
		var state string
		var timeval int64
		rows.Scan(&pid, &id, &kind, &state, &timeval)
		p := projects[pid]
		if p != nil {
			p.tasks = append(p.tasks, &task{id, states[kind], state, time.Unix(timeval, 0)})
			if len(p.tasks) > 10 {
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
			s := states[stateName]
			trigger, exists := p.triggers[t]
			if !exists {
				trigger.from = s
				trigger.states = make(map[state]bool, 0)
			}
			trigger.states[s] = true
			if s < trigger.from {
				trigger.from = s
			}
			p.triggers[t] = trigger
			switch s {
			case PREPARING:
				t.prepareDep = p
			case PREPACKAGING:
				t.prepackageDep = p
			case PACKAGING:
				t.packageDep = p
			case SCANNING:
				t.scanners = append(t.scanners, p)
			}
		}
	}
	rows, err = db.Query(`SELECT project, name, credential FROM environments`)
	for rows.Next() {
		var pid int
		var name string
		var crid int
		rows.Scan(&pid, &name, &crid)
		p := projects[pid]
		cr := credentials[crid]
		if p != nil && cr != nil {
			p.credentials[name] = cr
		}
	}

	go func() {
		for {
			select {
			case client := <-clients.register:
				clients.clients[client] = true
				logger.Infof("Registering event listener: %s", client)
			case client := <-clients.unregister:
				delete(clients.clients, client)
				logger.Infof("Unregistering event listener: %s", client)
			case event := <-clients.events:
				for client, _ := range clients.clients {
					client <- event
					logger.Infof("Sending event %s to listener: %s", event, client)
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

	templates, _ = template.ParseGlob("templates/*")

	handlers["/events"] = handleEvents
	handlers["/login"] = handleLogin
	handlers["/user/current"] = handleUserCurrent
	handlers["/user/login"] = handleUserLogin
	handlers["/user/logout"] = handleUserLogout
	handlers["/project/list"] = handleProjectList
	handlers["/project/graph"] = handleProjectGraph
	handlers["/project/status"] = handleProjectStatus
	handlers["/project/update"] = handleProjectUpdate
	handlers["/project/destinations"] = handleProjectDestinations
	handlers["/project/triggers"] = handleProjectTriggers
	handlers["/project/environment"] = handleProjectEnvironment
	handlers["/project/create"] = handleProjectCreate
	handlers["/project/upload"] = handleProjectUpload
	handlers["/project/config/list"] = handleProjectConfigList
	handlers["/project/config/read"] = handleProjectConfigRead
	handlers["/project/build"] = handleProjectBuild
	handlers["/project/delete"] = handleProjectDelete
	handlers["/task/list"] = handleTaskList
	handlers["/task/logs"] = handleTaskLogs
	handlers["/task/stop"] = handleTaskStop
	handlers["/registry/list"] = handleRegistryList
	handlers["/registry/create"] = handleRegistryCreate
	handlers["/registry/update"] = handleRegistryUpdate
	handlers["/registry/delete"] = handleRegistryDelete
	handlers["/credential/list"] = handleCredentialList
	handlers["/credential/create"] = handleCredentialCreate
	handlers["/credential/update"] = handleCredentialUpdate
	handlers["/credential/delete"] = handleCredentialDelete

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
