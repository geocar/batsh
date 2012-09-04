# normally you'll call this with make args...
# make common/lock.c
all: batsh
batsh: unix/batsh.c common/lock.c
