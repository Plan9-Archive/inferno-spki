#include <u.h>
#include <libc.h>
#include <thread.h>
#include <auth.h>
#include <9pclient.h>
#include <bio.h>

static int sendkey(char*);

void
threadmain(int argc, char **argv)
{
	char *s;
	Biobuf bin;

	ARGBEGIN{
	}ARGEND
	Binit(&bin, 0, OREAD);
	while((s = Brdline(&bin, '\n')) != nil){
		s[Blinelen(&bin)-1] = 0;
		if(sendkey(s) < 0)
			fprint(2, "feedkey: factotum says no: %r\n");
	}
	threadexitsall(nil);
}

static int
sendkey(char *s)
{
	int rv;
	CFid *fid;
	
	fid = nsopen("factotum", nil, "ctl", OWRITE);
	if(fid == nil)
		sysfatal("opening factotum/ctl: %r");
	rv = fswrite(fid, s, strlen(s));
	fsclose(fid);
	return rv;
}
