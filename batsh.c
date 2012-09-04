#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#include <errno.h>
#include <ctype.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <sys/file.h>
#include <time.h>

#include <limits.h>

static int trace = 0;
static char *home = 0;
static int twophase = -1;

#ifndef ARG_MAX
#define ARG_MAX	1024
#endif

#ifndef BATSH_DEFAULT_CONCURRENCY
#define BATSH_DEFAULT_CONCURRENCY 25
#endif

#ifndef BATSH_DEFAULT_MAXDEPTH
#define BATSH_DEFAULT_MAXDEPTH 10
#endif

#ifndef JOURNAL_STUB
#define JOURNAL_STUB ".qmail.jlog"
#endif

#ifndef CONCURRENCY_STUB
#define CONCURRENCY_STUB ".qmail.mproc"
#endif

#ifndef TEMPFILE_STUB
#define TEMPFILE_STUB	".qmail.qtmp"
#endif


static int sbaccess(int u, int g, struct stat *s, int m)
{
	if (s->st_uid == u) {
		if ((m << 6) & s->st_mode) return 1;
	}
	if (s->st_gid == g) {
		if ((m << 3) & s->st_mode) return 1;
	}
	if (m & s->st_mode) return 1;
	return 0;
}
static int confvar(const char *s)
{
	struct stat sb;
	const char *f;
	int st;

	while (isspace((int)*s)) s++;
	if (*s == '!') return ! confvar(s+1);

	if (*s == '$') return getenv(s+1) != NULL;
	if (s[0] == '-' && (s[1] == 'l' || s[1] == 'L')) {
		f = s+2;
		while (isspace((int)*f)) f++;
		if (lstat(f, &sb) == -1) return 0;
		if (S_ISLNK(sb.st_mode)) return 1;
		return 0;
	}
	if (*s == '[' || *s == '`') {
		/* rewind */
		if (lseek(0, 0, SEEK_SET) != (off_t)0) {
			if (trace) fprintf(stderr, "lseek SEEK_SET(%s)\n", strerror(errno));
			exit(111);
		}

		if (*s == '`') s++;
		while (isspace((int)*s)) s++;
		st = system(s);
		if (WIFEXITED(st) && WEXITSTATUS(st) == 0) return 1;
		if (!WIFEXITED(st) || WEXITSTATUS(st) == 127) {
			if (trace) fprintf(stderr, "%s = system(%s)\n", s, strerror(errno));
			exit(111);
		}
		return 0;
	}
	if (*s == '/' || *s == '.' || *s == '-') {
		if (*s == '-') {
			f = s+2;
			while (isspace((int)*f)) f++;
			if (!*f) return 0;
		} else {
			f = s;
		}

		if (stat(f, &sb) == -1) return 0;
		if (*s != '-' || s[1] == 'e') return 1;

		switch ((s[1])) {
		case 'r': return sbaccess(geteuid(), getegid(), &sb, 04);
		case 'w': return sbaccess(geteuid(), getegid(), &sb, 02);
		case 'x': return sbaccess(geteuid(), getegid(), &sb, 01);
		case 'o': return geteuid() == sb.st_uid;

		case 'R': return sbaccess(getuid(), getgid(), &sb, 04);
		case 'W': return sbaccess(getuid(), getgid(), &sb, 02);
		case 'X': return sbaccess(getuid(), getgid(), &sb, 01);
		case 'O': return getuid() == sb.st_uid;

		case 'z': return sb.st_size == 0;
		case 's': return sb.st_size != 0;

		case 'f': return S_ISREG(sb.st_mode);
		case 'd': return S_ISDIR(sb.st_mode);
		case 'p': return S_ISFIFO(sb.st_mode);
		case 'S': return S_ISSOCK(sb.st_mode);
		case 'b': return S_ISBLK(sb.st_mode);
		case 'c': return S_ISCHR(sb.st_mode);
		case 't': return 0;

		case 'u': return sb.st_mode & S_ISUID;
		case 'g': return sb.st_mode & S_ISGID;
		case 'k': return sb.st_mode & S_ISVTX;

		case 'T': return 1; /* sure */
		case 'B': return 1; /* sure */

		};
		/* otherwise, not true */
		return 0;
	}

	return 0;
}

static int last_wd = -1;
static int mcc = BATSH_DEFAULT_CONCURRENCY;

void dolock(int fd);
int trylock(int fd);

static void build_journal(char *jobs, int scriptfd);
static int cwrite(int fd, void *buf, size_t len);
static int cread(int fd, void *buf, size_t len);
static off_t read_record(int jh, unsigned char *st, char **cmd);
static void run_child(int jh, char *cmd, char *jobs);
static int build_jobs(FILE *fp, int th);
static void setup_build_jobs(FILE *fp, char *jobs);
static void do_jobs(int jh, char *jobs, int scriptfd);

static int cwrite(int fd, void *buf, size_t len)
{
	int r, x;
	for (x = 0; x < len; x++) {
		do {
			r = write(fd, (void *)(buf+x), len-x);
		} while (r == -1 && errno == EINTR);
		if (r < 1) return 0;
		x += r;
	}
	return 1;
}

static int cread(int fd, void *buf, size_t len)
{
	int r, x;
	for (x = 0; x < len; x++) {
		do {
			r = read(fd, (void *)(buf+x), len-x);
		} while (r == -1 && errno == EINTR);
		if (r == 0) return 0; 
		x += r;
	}
	return 1;
}

static off_t read_record(int jh, unsigned char *st, char **cmd)
{
	unsigned int len;
	off_t o;

	if (!cread(jh, &len, sizeof(unsigned int))) return (off_t)0;
	o = lseek(jh, 0, SEEK_CUR);
	if (o < 1) {
		/* impossible */
		return (off_t)-1;
	}

	if (!cread(jh, st, sizeof(unsigned char))) return (off_t)-1;
	*cmd = (char *)malloc(len+1);
	if (!*cmd) {
		if (trace) fprintf(stderr, "malloc(%s)\n", strerror(errno));
		exit(111);
	}
	if (!cread(jh, *cmd, len+1)) return (off_t)-1;
	cmd[0][len] = 0;

	return o;
}

/* schedule delivery as soon as is possible */
static char *closures = 0;
static unsigned int closures_len = 0;
static void add_closure(char *buf)
{
	unsigned int l;

	if (strcmp(buf, "&") == 0) {
		/* kill closures */
		free(closures);
		closures = 0;
		closures_len = 0;
		return;
	}

	l = strlen(buf)+1;
	closures = (char *)realloc(closures, closures_len + (l+1));
	if (!closures) {
		if (trace) fprintf(stderr, "realloc(%s)\n", strerror(errno));
		exit(111);
	}
	memcpy(closures+closures_len, buf, l);
	closures_len += l;
}
static void run_closures(void)
{
	unsigned int i, l;
	char *p;
	int st;

	for (i = 0, p = closures; i < closures_len;) {
		l = strlen(p)+1;
		st = system(p);
		if (WIFEXITED(st)) {
			if (trace) fprintf(stderr, "& %s = exited (%d)\n", p, WEXITSTATUS(st));
			if (WEXITSTATUS(st) != 0) {
				break;
			}
		} else {
			if (trace) fprintf(stderr, "& %s = killed\n", p);
			break;
		}

		p += l; i+= l;
	}
}

static void get_concurrency(void)
{
	if (mcc > 1) {
		static char mc_buffer[128];
		int i, fd, cx;

		for (i = cx = 0; !cx && i < mcc; i++) {
			sprintf(mc_buffer, 
					CONCURRENCY_STUB
					".concurrency-%d", i);
			fd = open(mc_buffer, O_RDWR|O_CREAT, 0600);
			if (fd > -1) {
				if (trylock(fd) == 1) {
					(void)fcntl(fd, F_SETFD, 0);
					cx = 1;
				} else {
					(void)close(fd);
				}
			}
		}
		if (!cx) {
			/* couldn't obtain concurrency */
			if (trace) fprintf(stderr, "no concurrency\n");
			exit(111);
		}
		/* fall through; got concurrency handle */
	}
}

static void run_child(int jh, char *cmd, char *jobs)
{
	char *p;
	int st, eflag;

	puts(cmd);
	/* return to working directory */
	if (fchdir(last_wd) == -1) {
		if (trace) fprintf(stderr, "fchdir(%s)\n", strerror(errno));
		run_closures();
		exit(111);
	}

	/* rewind */
	if (lseek(0, 0, SEEK_SET) != (off_t)0) {
		if (trace) fprintf(stderr, "lseek SEEK_SET(%s)\n", strerror(errno));
		exit(111);
	}

	eflag = 0;
	if (*cmd == '!') {
		if (!strncmp(cmd+1, "exit", 4)) {
			if (isspace(((unsigned int)cmd[5]))) {
				p = cmd+5;
				while (isspace(((unsigned int)*p))) p++;
				if (trace) fprintf(stderr, "exit(%d)\n", atoi(p));
				run_closures();
				if (chdir(home) != -1)
					(void) unlink(jobs); /* delete the job */
				if (trace) fprintf(stderr, "unlink(%s)\n", jobs);
				exit(atoi(p));
			}

		} else if (!strncmp(cmd+1, "exec", 4)) {
			if (isspace(((unsigned int)cmd[5]))) {
				if (trace) fprintf(stderr, "execute-flag on\n");
				eflag = 1;
			}
		}

		st = system(cmd+1);
		if (st == -1) {
			if (trace) fprintf(stderr, "%s = system(%s)\n", cmd, strerror(errno));
			run_closures();
			exit(111);
		}
		if (trace) fprintf(stderr, "returned with st: %x\n", st);

	} else if (*cmd == '|') {
		pid_t p;
		switch ((p = fork())) {
		case -1:
			if (trace) fprintf(stderr, "fork(%s)\n", strerror(errno));
			exit(111);
		case 0:
			/* child */
			if (!trace) {
				(void) close(1);
				(void) close(2);
			}
			get_concurrency();
			st = system(cmd+1);
			if (st == -1) {
				if (trace)
					fprintf(stderr, "%s = system(%s)\n", cmd, strerror(errno));
				exit(111);
			}
			break;
		default:
			/* parent */
			if (trace) fprintf(stderr, "batsh/fork()\n");
			exit(111);
		};
	} else {
		if (trace) fprintf(stderr, "%s = unknown tooling\n", cmd);
		exit(111);
	}

	/* check status */
	if (WIFEXITED(st)) {
		unsigned char sq[1];
		sq[0] = WEXITSTATUS(st);

		if (trace) {
			if (sq[0] == 127) {
				fprintf(stderr, "%s = system failed\n", cmd);
			} else {
				fprintf(stderr, "%s = %d\n", cmd, (int)sq[0]);
			}
		}

		if (sq[0] == 97) sq[0] = 0; /* hack- continue processing */

		if (sq[0] == 127 || sq[0] == 111) {
			run_closures();
			exit(111);
		}
		if (!cwrite(jh, sq, 1)) {
			if (trace) fprintf(stderr, "Failed to write to journal: %s\n", strerror(errno));
			run_closures();
			exit(111);
		}
		if (*cmd == '!') {
			if (sq[0] == 0 && !eflag) {
				if (trace) fprintf(stderr, "!return\n");
				return; /* only path for return! */
			}
			if (chdir(home) != -1)
				(void) unlink(jobs); /* delete the job */
		}
		run_closures();
		if (sq[0] == 98) sq[0] = 0; /* hack2 */
		exit(sq[0]);
	} else {
		/* other failure */
		run_closures();
		if (trace) fprintf(stderr, "%s = killed\n", cmd);
		exit(111);
	}
}

static void setup_build_jobs(FILE *sc, char *jobs)
{
	/* must be bigger than TEMPFILE_STUB+64-or-so characters */
	static char line[1024];
	int th, i;

	i = 0;
	do {
		sprintf(line, TEMPFILE_STUB ".batsh.%lu.%lu.%u",
					(unsigned long)time(0),
					(unsigned long)getpid(),
					i++);
		th = open(line, O_CREAT|O_EXCL|O_WRONLY, 0600);
	} while (th == -1 && (errno == EINTR
#ifdef EAGAIN
				|| errno == EAGAIN
#endif
				|| errno == EEXIST));
	if (th == -1) {
		if (trace) fprintf(stderr, "open/qtmp()\n");
		exit(111);
	}

	if (!build_jobs(sc, th)) {
		close(th);
		unlink(line);
		if (trace) fprintf(stderr, "build_jobs()\n");
		exit(111);
	}

	if (close(th) == -1) {
		unlink(line);
		if (trace) fprintf(stderr, "close(%s)\n", strerror(errno));
		exit(111);
	}
	
	if (rename(line, jobs) == -1) {
		unlink(line);
		if (trace) fprintf(stderr, "rename(%s)\n", strerror(errno));
		exit(111);
	}
}

static int build_jobs(FILE *sc, int th)
{
	unsigned int len;
	static char linebuf[ARG_MAX];
	char *line;
	int i;

	while (fgets(linebuf, sizeof(linebuf) - 1, sc)) {
		for (i = 0; isspace(((int)linebuf[i])); i++);
		if (! linebuf[i]) continue;
		line = &linebuf[i];

		if (*line == '#') continue;

		len = strlen(line);
		if (line[0] == '<') {
			FILE *fp;
			/* relative to $HOME! */
			fp = fopen(line+1, "r");
			if (!fp) continue;
			if (!build_jobs(fp, th)) {
				fclose(fp);
				return 0;
			}
			fclose(fp);
		} else {
			unsigned char cs[sizeof(len)+2];
			unsigned char *qx;

			if (strchr("|!?+-;&", *line) == 0) {
				cs[sizeof(len)+1] = '|';
				qx = line;
			} else {
				cs[sizeof(len)+1] = *line;
				qx = line+1;
				len--;
			}

			memcpy(cs, &len, sizeof(len));
			cs[sizeof(len)] = 111;

			if (!cwrite(th, cs, sizeof(cs))) return 0;
			if (!cwrite(th, qx, strlen(qx))) return 0;
		}
	} 
	return 1;
}



static void build_journal(char *jobs, int scriptfd)
{
	int jh;
	struct stat s, j;


	if (fstat(scriptfd, &s) == -1) {
		if (trace) fprintf(stderr, "fstat(%s)\n", strerror(errno));
		exit(111);
	}
	if (s.st_mode & 022) {
		if (trace) fprintf(stderr, "scriptfd = world writable\n");
		exit(111); /* world writable bombout! */
	}

REOPEN:
	jh = open(jobs, O_RDWR|O_NOCTTY);
	if (jh == -1 || fstat(jh, &j) == -1 || (s.st_mtime > j.st_mtime))  {
		FILE *fp;
		int xfd;

		if (jh != -1) {
			dolock(jh);
		}

		if (trace) fprintf(stderr, "mtime(%lu) <=> mtime(%lu)\n",
					(unsigned long)s.st_mtime,
					(unsigned long)j.st_mtime);
		xfd = dup(scriptfd);
		if (xfd == -1) {
			if (trace) fprintf(stderr, "dup(%s)\n", strerror(errno));
			exit(111);
		}

		fp = fdopen(xfd, "r");

		if (!fp) {
			if (trace) fprintf(stderr, "fdopen(%s)\n", strerror(errno));
			exit(111);
		}
		setup_build_jobs(fp, jobs);

		fclose(fp);
		(void) close(jh);
		goto REOPEN;
	}

	if (fstat(jh, &j) == -1) {
		if (trace) fprintf(stderr, "fstat(%s)\n", strerror(errno));
		exit(111);
	}
	if (j.st_mode & 022) {
		if (trace) fprintf(stderr, "jobsfd = world writable\n");
		exit(111); /* world writable bombout! */
	}

	if (trylock(jh) == 1) {
		(void)close(twophase);
		twophase = -1;

		do_jobs(jh, jobs, scriptfd);
		if (trace) fprintf(stderr, "do_jobs returned?\n");
	} else {
		if (trace) fprintf(stderr, "journal already locked\n");
	}
	exit(111);
}

extern char **environ;
/* because unsetenv is unportable */
static void remove_from_env(const char *s)
{
	int i, j;

	j = strlen(s);
	for (i = 0; environ[i]; i++){ 
		if (strncmp(environ[i], s, j) == 0
			&& environ[i][j] == '=') {
			for (j = i+1; environ[j]; j++) {
				environ[j-1] = environ[j];
			}
			environ[j-1] = 0;
			return;
		}
	}
}

static void do_jobs(int jh, char *jobs, int scriptfd) 
{
	unsigned char st;
	int skip = 0;
	off_t r, p;

	char *cmd = 0;
	while ((r = read_record(jh, &st, &cmd)) > 0) {
		if (st == 0) {
			free(cmd);
			continue;

		} else if (st == 111) {
			if (*cmd == ';') {
				free(cmd);
				if (skip > 0) skip--;
				continue;

			} else if (skip) {
				if (*cmd == '?') skip++;
				free(cmd);
				continue;
			}
			if (*cmd == '+') {
				if (putenv(cmd+1) == -1) {
					if (trace) fprintf(stderr, "putenv(%s)\n", strerror(errno));
					exit(111);
				}
				continue;

			} else if (*cmd == '-') {
				remove_from_env(cmd+1);
				free(cmd);
				continue;

			} else if (*cmd == '?') {
				if (confvar(cmd+1) != 0) {
					free(cmd);
					continue;
				}
				/* hrm... not in env... skipmode */
				skip++;
				free(cmd);
				continue;

			} else if (*cmd == '&') {
				add_closure(cmd+1);
				free(cmd);
				continue;
			}

			p = lseek(jh, 0, SEEK_CUR);
			if (p == (off_t)-1) {
				if (trace) fprintf(stderr, "lseek SEEK_CUR(%s)\n", strerror(errno));
				exit(111);
			}
			if (lseek(jh, r, SEEK_SET) != r) {
				if (trace) fprintf(stderr, "lseek SEEK_SET(%s)\n", strerror(errno));
				exit(111);
			}
			run_child(jh, cmd, jobs);
			free(cmd);
			if (lseek(jh, p, SEEK_SET) != p) {
				if (trace) fprintf(stderr, "lseek SEEK_SET(%s)\n", strerror(errno));
				exit(111);
			}

		} else {
			if (st == 98) st = 0;
			if (trace) fprintf(stderr, "journal command exit: %d\n", st);
			if (chdir(home) != -1)
				(void) unlink(jobs);
			exit(st);
		}
	}
	if (r == (off_t)-1) {
		if (trace) fprintf(stderr, "script changing too fast\n");
		exit(111); /* eek... try again later */
	}
	/* all done! if we get here, then r == 0, and we're at the
	 * end of the file.
	 */
	if (chdir(home) != -1)
		(void) unlink(jobs);
	if (trace) fprintf(stderr, "script completion\n");
	exit(0);
}

static int capture_int(const char *f, int def)
{
	FILE *fp;
	int o = 0, c;
	fp = fopen(f, "r");
	if (!fp) return def;
	for (;;) {
		c = fgetc(fp);
		if (c == -1) break;
		if (!isdigit(c)) break;

		o *= 10;
		o += (c - '0');
	}
	(void) fclose(fp);
	if (o == 0) return def;
	return o;
}

int main(int argc, char **argv) 
{
	static char sb[64];
	char *recipient, *jobs;
	struct stat inf;
	struct stat sinf;
	char *q;
	int bl = 0;
	int bm;
	int fd;

	recipient = getenv("RECIPIENT");
	if (!recipient) {
		recipient = "";
	} else {
		for (q = recipient; *q; q++)
			if (*q == '@') *q = '=';
			else if (*q == '.') *q = ':';
			else if (*q == '/') *q = '_';
	}
	jobs = malloc(sizeof(JOURNAL_STUB) + 64 + strlen(recipient));
	if (!jobs) {
		perror("malloc");
		exit(1);
	}

	trace = (getenv("BATSH_TRACE")) ? 1 : 0;
	if (trace) setlinebuf(stderr);
	if (trace) fprintf(stderr, "batsh starting up\n");

	/* set concurrency */
	q = (char *)getenv("BATSH_CONCURRENCY");
	if (!q) mcc = capture_int("/etc/batsh.concurrency", BATSH_DEFAULT_CONCURRENCY);
	else {
		mcc = atoi(q);
		if (mcc < 1) mcc = capture_int("/etc/batsh.concurrency", BATSH_DEFAULT_CONCURRENCY);
	}

	/* depth limit */
	q = (char *)getenv("BATSH_MAXDEPTH");
	if (!q) bm = BATSH_DEFAULT_MAXDEPTH;
	else {
		bm = atoi(q);
		if (bm < 1) bm = BATSH_DEFAULT_MAXDEPTH;
	}

	/* increment batsh level (depthfinder) */
	q = (char *)getenv("BATSH_LEVEL");
	if (q) bl = atoi(q);
	if (bl < 1) {
		bl = 1;
	} else if (bl > bm) {
		fprintf(stderr, "$BATSH_LEVEL greater than $BATSH_MAXDEPTH (%d > %d)\n", bl, bm);
		exit(1);
	} else {
		bl++;
	}
	sprintf(sb, "BATSH_LEVEL=%d", bl);
	putenv(sb);

	if (fstat(0, &inf) == -1) {
		if (trace) fprintf(stderr, "Can't fstat() stdin: %s\n", strerror(errno));
		exit(111);
	}
	if (lseek(0, 0, SEEK_SET) != (off_t)0
			|| argc != 2 || !S_ISREG(inf.st_mode)) {
		fprintf(stderr, "Usage: #!batsh < qmess\n");
		exit(1); 
	}

	last_wd = open(".", O_RDONLY);
	if (last_wd == -1) {
		if (trace) fprintf(stderr, "open(.): %s\n", strerror(errno));
		exit(111); /* no current working directory? */
	}

	q = (char *)getenv("HOME");
	if (!q) {
		fprintf(stderr, "$HOME is unset\n");
		exit(1);
	}
	home = strdup(q);
	if (!home) {
		if (trace) fprintf(stderr, "Can't strdup(): %s\n", strerror(errno));
		exit(111);
	}

	twophase = open(".email/.svfilter.twophase", O_CREAT|O_RDWR,0600);
	if (twophase == -1) {
		if (trace) fprintf(stderr, "Cannot open two-phase lock head: %s\n",strerror(errno));
		if (trylock(twophase) != 1) {
			if (trace) fprintf(stderr, "another twophase holder open\n");
			exit(111);
		}
	}

	fd = open(argv[1], O_RDONLY|O_NOCTTY);
	if (fd == -1) {
		if (trace) fprintf(stderr, "open(%s): %s\n", argv[1], strerror(errno));
		exit(111);
	}
	if (fstat(fd, &sinf) == -1) {
		if (trace) fprintf(stderr, "Can't fstat() script: %s\n", strerror(errno));
		exit(111);
	}

	if (chdir(home) == -1) {
		if (trace) fprintf(stderr, "Can't chdir(%s): %s\n", q, strerror(errno));
		exit(111);
	}

	sprintf(jobs, "%s.%lx:%lx.%lx:%lx;%s", JOURNAL_STUB,
			(long int)inf.st_dev,  (long int)inf.st_ino,
			(long int)sinf.st_dev, (long int)sinf.st_ino,
			recipient);
	
	build_journal(jobs, fd);

	/* should not reach */
	if (trace) fprintf(stderr, "Should not reach\n");
	exit(1);
}
