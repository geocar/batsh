#if !defined(USE_FLOCK) && !defined(USE_LOCKF) && !defined(USE_FCNTL) && !defined(NO_LOCKING)
#error "Either -DUSE_FLOCK, -DUSE_LOCKF, -DUSE_FCNTL, _or_ -DNO_LOCKING and know the consequences"
#endif

#include <sys/stat.h>
#include <sys/types.h>
#include <sys/file.h>
#include <unistd.h>
#include <fcntl.h>
#include <errno.h>


static int lockhelper(int fd, int hold)
{
	int r;

	errno = 0;
	do {
#if defined(USE_FLOCK)
		r = flock(fd, LOCK_EX | (hold ? LOCK_NB : 0));
#elif defined(USE_LOCKF)
		r = lockf(fd, hold ? F_TLOCK : F_LOCK, 0);
#elif defined(USE_FCNTL)
		{
			struct flock fk;
			fk.l_type = F_WRLCK;
			fk.l_whence = SEEK_SET;
			fk.l_start = 0;
			fk.l_len = 0;
			r = fcntl(fd, (hold ? F_SETLK : F_SETLKW), (long)&fk);
		};
#elif !defined(NO_LOCKING)
		{
			struct stat sb;
			r = fstat(fd, &sb);
			if (r != -1 && sb.st_nlink > 1) r = -1;
		};
#else
		r = -1;
#endif
	} while (r == -1 && errno == EINTR);
	if (r == -1) {
		if (
#ifdef EAGAIN
		errno == EAGAIN ||
#endif
#ifdef EWOULDBLOCK
		errno == EWOULDBLOCK ||
#endif
#ifdef EACCES
		errno == EACCES ||
#endif
		0) {
			/* locked */
			return -1; /* already locked */
		}
		/* other failure */
		return 0;
	}
	/* we have the lock */
	return 1;
}

int trylock(int fd)
{
	return lockhelper(fd, 1);
}
void dolock(int fd)
{
	while (lockhelper(fd, 0) != 1);
}
