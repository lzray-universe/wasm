#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <cmath>

#if !defined(FORCE_32BIT_LIMB)&&defined(__SIZEOF_INT128__)&&!(defined(_MSC_VER)&&!defined(__clang__))
#define LIMB64 1
typedef uint64_t limb_t;
typedef unsigned __int128 dlimb_t;
enum{LIMB_BITS=64};
#else
#define LIMB64 0
typedef uint32_t limb_t;
typedef uint64_t dlimb_t;
enum{LIMB_BITS=32};
#endif

#define FAST_DIV_RECIP 0
#define OUTPUT_DC_CUT_DIGITS 50000
#define KARAT_CUT 128

#if LIMB64
#define OUT_BASE 1000000000000000000ULL
#define OUT_W 18
#else
#define OUT_BASE 1000000000ULL
#define OUT_W 9
#endif

struct ar{
	uint8_t**b;
	size_t*s;
	int nb,cap,cur;
	size_t u;
	size_t up(size_t x,size_t a);
	void init();
	void add(size_t n);
	void*alc(size_t n);
	void rst();
};

struct b{
	limb_t*a;
	int n,cap,own;
};

struct s{
	b v;
	int s;
};

struct pn{
	b p;
	int e;
	pn*l;
	pn*r;
};

ar ga;
int ao=1;

size_t ar::up(size_t x,size_t a){
	return (x+(a-1))&~(a-1);
}

void ar::init(){
	b=0;
	s=0;
	nb=0;
	cap=0;
	cur=0;
	u=0;
}

void ar::add(size_t n){
	size_t w=n,base=1u<<20;
	if(nb){
		size_t prev=s[cur];
		if(prev>base){
			base=prev;
		}
	}
	if(w<base){
		w=base;
	}
	w=up(w,64);
	if(nb==cap){
		cap=cap?cap*2:8;
		void*nbp=realloc(b,(size_t)cap*sizeof(*b));
		void*nsp=realloc(s,(size_t)cap*sizeof(*s));
		if(!nbp||!nsp){
			exit(1);
		}
		b=(uint8_t**)nbp;
		s=(size_t*)nsp;
	}
	b[nb]=(uint8_t*)malloc(w);
	if(!b[nb]){
		exit(1);
	}
	s[nb]=w;
	cur=nb;
	nb++;
	u=0;
}

void* ar::alc(size_t n){
	n=up(n,16);
	if(!nb){
		add(n);
	}
	if(u+n>s[cur]){
		add(n);
	}
	void*p=b[cur]+u;
	u+=n;
	return p;
}

void ar::rst(){
	if(!nb){
		return;
	}
	int best=0;
	for(int i=1;i<nb;i++){
		if(s[i]>s[best]){
			best=i;
		}
	}
	cur=best;
	u=0;
}

void bi(b&x){
	x.a=0;
	x.n=0;
	x.cap=0;
	x.own=1;
}

void fit(b&x,int m){
	if(m<=x.cap&&x.own){
		return;
	}
	limb_t*na;
	size_t bytes=(size_t)m*sizeof(limb_t);
	if(ao){
		na=(limb_t*)ga.alc(bytes);
		if(x.n){
			memcpy(na,x.a,(size_t)x.n*sizeof(limb_t));
		}
	}else{
		na=(limb_t*)realloc(x.own?x.a:0,bytes);
		if(!na){
			exit(1);
		}
		if(!x.own&&x.n){
			memcpy(na,x.a,(size_t)x.n*sizeof(limb_t));
		}
	}
	x.a=na;
	x.cap=m;
	x.own=1;
}

void nrm(b&x){
	while(x.n&&x.a[x.n-1]==0){
		x.n--;
	}
}

void zer(b&x){
	x.n=0;
}

void ens(b&x,int m){
	if(m>x.n){
		fit(x,m);
		memset(x.a+x.n,0,(size_t)(m-x.n)*sizeof(limb_t));
		x.n=m;
	}
}

void setu(b&x,uint64_t v){
#if LIMB64
	fit(x,1);
	x.a[0]=(limb_t)v;
	if(x.a[0]){
		x.n=1;
	}else{
		x.n=0;
	}
#else
	fit(x,2);
	x.a[0]=(uint32_t)v;
	x.a[1]=(uint32_t)(v>>32);
	if(x.a[1]){
		x.n=2;
	}else if(x.a[0]){
		x.n=1;
	}else{
		x.n=0;
	}
#endif
}

void cpy(b&d,const b&s2){
	fit(d,s2.n);
	if(s2.n>0){
		memcpy(d.a,s2.a,(size_t)s2.n*sizeof(limb_t));
	}
	d.n=s2.n;
}

int cmp(const b&a,const b&b2){
	if(a.n!=b2.n){
		if(a.n>b2.n){
			return 1;
		}else{
			return -1;
		}
	}
	for(int i=a.n;i--;){
		limb_t x=a.a[i],y=b2.a[i];
		if(x!=y){
			if(x>y){
				return 1;
			}else{
				return -1;
			}
		}
	}
	return 0;
}

int clz_l(limb_t x){
	if(!x){
		return LIMB_BITS;
	}
	int n=0;
#if LIMB64
	int i=63;
	while(i>=0&&(((uint64_t)x>>i)&1)==0){
		n++;
		i--;
	}
#else
	int i=31;
	while(i>=0&&(((uint32_t)x>>i)&1)==0){
		n++;
		i--;
	}
#endif
	return n;
}

int blen(const b&x){
	if(!x.n){
		return 0;
	}
	limb_t h=x.a[x.n-1];
	return (x.n-1)*LIMB_BITS+(LIMB_BITS-clz_l(h));
}

void add(b&r,const b&a,const b&b2){
	int n=a.n>b2.n?a.n:b2.n;
	fit(r,n+1);
	dlimb_t c=0;
	for(int i=0;i<n;i++){
		dlimb_t s2=c;
		if(i<a.n){
			s2+=a.a[i];
		}
		if(i<b2.n){
			s2+=b2.a[i];
		}
		r.a[i]=(limb_t)s2;
		c=s2>>LIMB_BITS;
	}
	r.a[n]=(limb_t)c;
	r.n=n+1;
	nrm(r);
}

void sub(b&r,const b&a,const b&b2){
	fit(r,a.n);
	limb_t br=0;
	for(int i=0;i<a.n;i++){
		dlimb_t x=a.a[i],y=(dlimb_t)br;
		if(i<b2.n){
			y+=(dlimb_t)b2.a[i];
		}
		dlimb_t z=x-y;
		r.a[i]=(limb_t)z;
		br=(y>x);
	}
	r.n=a.n;
	nrm(r);
}

void mul_u64i(b&x,uint64_t m){
	if(!x.n||!m){
		x.n=0;
		return;
	}
	fit(x,x.n+(LIMB64?2:3));
	dlimb_t c=0;
	for(int i=0;i<x.n;i++){
		dlimb_t cur=c+(dlimb_t)x.a[i]*(dlimb_t)m;
		x.a[i]=(limb_t)cur;
		c=cur>>LIMB_BITS;
	}
	while(c){
		x.a[x.n]=(limb_t)c;
		x.n++;
		c>>=LIMB_BITS;
	}
	nrm(x);
}

void mul_u32i(b&x,uint32_t m){
	mul_u64i(x,(uint64_t)m);
}

void shl(b&y,const b&x,int s2){
	if(!x.n){
		y.n=0;
		return;
	}
	if(!s2){
		cpy(y,x);
		return;
	}
	fit(y,x.n+1);
	limb_t c=0;
	for(int i=0;i<x.n;i++){
		dlimb_t cur=((dlimb_t)x.a[i]<<s2)|(dlimb_t)c;
		y.a[i]=(limb_t)cur;
		c=(limb_t)(cur>>LIMB_BITS);
	}
	y.a[x.n]=c;
	y.n=x.n+1;
	nrm(y);
}

void shr(b&y,const b&x,int s2){
	if(!x.n){
		y.n=0;
		return;
	}
	if(!s2){
		cpy(y,x);
		return;
	}
	fit(y,x.n);
	limb_t c=0;
	for(int i=x.n;i--;){
		limb_t nc=(limb_t)(x.a[i]<<(LIMB_BITS-s2));
		y.a[i]=(limb_t)((x.a[i]>>s2)|c);
		c=nc;
	}
	y.n=x.n;
	nrm(y);
}

void lshi(b&x,int k){
	if(!x.n||!k){
		return;
	}
	int w=k/LIMB_BITS,bb=k%LIMB_BITS;
	fit(x,x.n+w+2);
	for(int i=x.n;i--;){
		x.a[i+w]=x.a[i];
	}
	for(int i=0;i<w;i++){
		x.a[i]=0;
	}
	x.n+=w;
	if(bb){
		limb_t c=0;
		for(int i=0;i<x.n;i++){
			dlimb_t cur=((dlimb_t)x.a[i]<<bb)|(dlimb_t)c;
			x.a[i]=(limb_t)cur;
			c=(limb_t)(cur>>LIMB_BITS);
		}
		if(c){
			x.a[x.n]=c;
			x.n++;
		}
	}
}

void rshw(b&y,const b&x,int w){
	if(x.n<=w){
		y.n=0;
		return;
	}
	int n=x.n-w;
	fit(y,n);
	memcpy(y.a,x.a+w,(size_t)n*sizeof(limb_t));
	y.n=n;
}

void truncb(b&x,int p){
	if(!p){
		x.n=0;
		return;
	}
	int w=p/LIMB_BITS,bb=p%LIMB_BITS,nn=w+(bb?1:0);
	if(x.n>nn){
		x.n=nn;
	}
	if(bb&&x.n){
#if LIMB64
		limb_t mask;
		if(bb==64){
			mask=~(limb_t)0;
		}else{
			mask=((limb_t)1<<bb)-1;
		}
#else
		limb_t mask=(limb_t)((1u<<bb)-1);
#endif
		x.a[x.n-1]&=mask;
	}
	nrm(x);
}

void shr1(b&x){
	limb_t c=0;
	for(int i=x.n;i--;){
		limb_t nc=(limb_t)(x.a[i]&1);
		x.a[i]=(limb_t)((x.a[i]>>1)|(c<<(LIMB_BITS-1)));
		c=nc;
	}
	nrm(x);
}

void addsh(b&d,const b&s2,int sh){
	if(!s2.n){
		return;
	}
	int need=sh+s2.n+2;
	ens(d,need);
	dlimb_t c=0;
	for(int i=0;i<s2.n;i++){
		dlimb_t cur=(dlimb_t)d.a[sh+i]+(dlimb_t)s2.a[i]+c;
		d.a[sh+i]=(limb_t)cur;
		c=cur>>LIMB_BITS;
	}
	int idx=sh+s2.n;
	while(c){
		dlimb_t cur=(dlimb_t)d.a[idx]+c;
		d.a[idx]=(limb_t)cur;
		c=cur>>LIMB_BITS;
		idx++;
		if(idx>=d.n){
			ens(d,idx+1);
		}
	}
	nrm(d);
}

void slic(b&out,const b&in,int st,int len){
	out.own=0;
	out.cap=0;
	if(st>=in.n){
		out.a=0;
		out.n=0;
		return;
	}
	int n=in.n-st;
	if(n>len){
		n=len;
	}
	out.a=in.a+st;
	out.n=n;
	while(out.n&&out.a[out.n-1]==0){
		out.n--;
	}
}

void ms(b&r,const b&a,const b&b2){
	if(!a.n||!b2.n){
		r.n=0;
		return;
	}
	int n=a.n,m=b2.n;
	fit(r,n+m+1);
	memset(r.a,0,(size_t)(n+m+1)*sizeof(limb_t));
	for(int i=0;i<n;i++){
		dlimb_t c=0;
		for(int j=0;j<m;j++){
			dlimb_t cur=c+(dlimb_t)r.a[i+j]+(dlimb_t)a.a[i]*(dlimb_t)b2.a[j];
			r.a[i+j]=(limb_t)cur;
			c=cur>>LIMB_BITS;
		}
		int k=i+m;
		while(c){
			dlimb_t cur=(dlimb_t)r.a[k]+c;
			r.a[k]=(limb_t)cur;
			c=cur>>LIMB_BITS;
			k++;
		}
	}
	r.n=n+m+1;
	nrm(r);
}

void mk(b&r,const b&a,const b&b2){
	if(!a.n||!b2.n){
		r.n=0;
		return;
	}
	if(a.n<KARAT_CUT||b2.n<KARAT_CUT){
		ms(r,a,b2);
		return;
	}
	int n=a.n>b2.n?a.n:b2.n,m=n>>1;
	b a0,a1,b0,b1,z0,z1,z2,sa,sb,t;
	bi(a0);
	bi(a1);
	bi(b0);
	bi(b1);
	bi(z0);
	bi(z1);
	bi(z2);
	bi(sa);
	bi(sb);
	bi(t);
	slic(a0,a,0,m);
	slic(a1,a,m,a.n-m);
	slic(b0,b2,0,m);
	slic(b1,b2,m,b2.n-m);
	add(sa,a0,a1);
	add(sb,b0,b1);
	mk(z0,a0,b0);
	mk(z2,a1,b1);
	mk(z1,sa,sb);
	if(cmp(z1,z0)<0){
		ms(r,a,b2);
		return;
	}
	sub(t,z1,z0);
	if(cmp(t,z2)<0){
		ms(r,a,b2);
		return;
	}
	sub(z1,t,z2);
	zer(r);
	addsh(r,z0,0);
	addsh(r,z1,m);
	addsh(r,z2,2*m);
}

void mul(b&r,const b&a,const b&b2){
	if(&r==&a||&r==&b2){
		b t;
		bi(t);
		mk(t,a,b2);
		cpy(r,t);
		return;
	}
	mk(r,a,b2);
}

void dms(b&q,b&r,const b&u,limb_t v){
	fit(q,u.n);
	dlimb_t rem=0;
	for(int i=u.n;i--;){
		dlimb_t cur=(rem<<LIMB_BITS)|(dlimb_t)u.a[i];
		q.a[i]=(limb_t)(cur/(dlimb_t)v);
		rem=cur%(dlimb_t)v;
	}
	q.n=u.n;
	nrm(q);
	setu(r,(uint64_t)rem);
}

#if LIMB64&&FAST_DIV_RECIP
void qrr(uint64_t&qh,dlimb_t&rh,limb_t uh,limb_t ul,limb_t vh,long double inv){
	long double uld=ldexpl((long double)uh,64)+(long double)ul;
	long double qld=uld*inv;
	if(qld<0){
		qld=0;
	}
	if(qld>18446744073709551615.0L){
		qld=18446744073709551615.0L;
	}
	uint64_t q=(uint64_t)qld;
	dlimb_t u=((dlimb_t)uh<<64)|(dlimb_t)ul,v=(dlimb_t)vh;
	while((dlimb_t)q*v>u){
		q--;
	}
	qh=q;
	rh=u-(dlimb_t)q*v;
}
#endif

void divq(b&q,const b&u,const b&v){
	if(!v.n){
		exit(1);
	}
	int cu=cmp(u,v);
	if(cu<0){
		setu(q,0);
		return;
	}
	if(v.n==1){
		b rr;
		bi(rr);
		dms(q,rr,u,v.a[0]);
		return;
	}
	int n=v.n,m=u.n-v.n;
	b vn,un;
	bi(vn);
	bi(un);
	int ss=clz_l(v.a[n-1]);
	shl(vn,v,ss);
	shl(un,u,ss);
	fit(un,un.n+1);
	un.a[un.n]=0;
	un.n++;
	fit(q,m+1);
	memset(q.a,0,(size_t)(m+1)*sizeof(limb_t));
	q.n=m+1;
	dlimb_t base=(dlimb_t)1<<LIMB_BITS;
#if LIMB64&&FAST_DIV_RECIP
	long double inv=1.0L/(long double)vn.a[n-1];
#endif
	for(int j=m;j>=0;j--){
#if LIMB64&&FAST_DIV_RECIP
		uint64_t qh;
		dlimb_t rh;
		qrr(qh,rh,un.a[j+n],un.a[j+n-1],vn.a[n-1],inv);
		if((dlimb_t)qh>=base){
			qh=(uint64_t)(base-1);
			dlimb_t ujn=((dlimb_t)un.a[j+n]<<64)|(dlimb_t)un.a[j+n-1];
			rh=ujn-(dlimb_t)qh*(dlimb_t)vn.a[n-1];
		}
#else
		dlimb_t ujn=((dlimb_t)un.a[j+n]<<LIMB_BITS)|(dlimb_t)un.a[j+n-1],qhat=ujn/(dlimb_t)vn.a[n-1],rh=ujn%(dlimb_t)vn.a[n-1];
		limb_t qh;
		if(qhat>=base){
			qhat=base-1;
			rh+=vn.a[n-1];
		}
		qh=(limb_t)qhat;
#endif
#if LIMB64&&FAST_DIV_RECIP
		while(qh&&rh<base&&(dlimb_t)qh*(dlimb_t)vn.a[n-2]>((rh<<64)|(dlimb_t)un.a[j+n-2])){
			qh--;
			rh+=vn.a[n-1];
		}
		limb_t qhl=(limb_t)qh;
#else
		while(qh&&rh<base&&(dlimb_t)qh*(dlimb_t)vn.a[n-2]>((rh<<LIMB_BITS)|(dlimb_t)un.a[j+n-2])){
			qh--;
			rh+=vn.a[n-1];
		}
		limb_t qhl=qh;
#endif
		limb_t bor=0,car=0;
		for(int i=0;i<n;i++){
			dlimb_t p=(dlimb_t)vn.a[i]*(dlimb_t)qhl+(dlimb_t)car;
			car=(limb_t)(p>>LIMB_BITS);
			limb_t subtr=(limb_t)p,cur=un.a[j+i];
			dlimb_t t=(dlimb_t)subtr+(dlimb_t)bor;
			un.a[j+i]=(limb_t)((dlimb_t)cur-t);
			bor=(t>(dlimb_t)cur);
		}
		limb_t cur=un.a[j+n];
		dlimb_t t=(dlimb_t)car+(dlimb_t)bor;
		un.a[j+n]=(limb_t)((dlimb_t)cur-t);
		int neg=(t>(dlimb_t)cur);
		q.a[j]=qhl;
		if(neg){
			q.a[j]--;
			dlimb_t c=0;
			for(int i=0;i<n;i++){
				dlimb_t sum=(dlimb_t)un.a[j+i]+(dlimb_t)vn.a[i]+c;
				un.a[j+i]=(limb_t)sum;
				c=sum>>LIMB_BITS;
			}
			un.a[j+n]=(limb_t)((dlimb_t)un.a[j+n]+c);
		}
	}
	nrm(q);
}

void divm(b&q,b&r,const b&u,const b&v){
	if(!v.n){
		exit(1);
	}
	int cu=cmp(u,v);
	if(cu<0){
		setu(q,0);
		cpy(r,u);
		return;
	}
	if(v.n==1){
		dms(q,r,u,v.a[0]);
		return;
	}
	int n=v.n,m=u.n-v.n;
	b vn,un;
	bi(vn);
	bi(un);
	int ss=clz_l(v.a[n-1]);
	shl(vn,v,ss);
	shl(un,u,ss);
	fit(un,un.n+1);
	un.a[un.n]=0;
	un.n++;
	fit(q,m+1);
	memset(q.a,0,(size_t)(m+1)*sizeof(limb_t));
	q.n=m+1;
	dlimb_t base=(dlimb_t)1<<LIMB_BITS;
#if LIMB64&&FAST_DIV_RECIP
	long double inv=1.0L/(long double)vn.a[n-1];
#endif
	for(int j=m;j>=0;j--){
#if LIMB64&&FAST_DIV_RECIP
		uint64_t qh;
		dlimb_t rh;
		qrr(qh,rh,un.a[j+n],un.a[j+n-1],vn.a[n-1],inv);
		if((dlimb_t)qh>=base){
			qh=(uint64_t)(base-1);
			dlimb_t ujn=((dlimb_t)un.a[j+n]<<64)|(dlimb_t)un.a[j+n-1];
			rh=ujn-(dlimb_t)qh*(dlimb_t)vn.a[n-1];
		}
#else
		dlimb_t ujn=((dlimb_t)un.a[j+n]<<LIMB_BITS)|(dlimb_t)un.a[j+n-1],qhat=ujn/(dlimb_t)vn.a[n-1],rh=ujn%(dlimb_t)vn.a[n-1];
		limb_t qh;
		if(qhat>=base){
			qhat=base-1;
			rh+=vn.a[n-1];
		}
		qh=(limb_t)qhat;
#endif
#if LIMB64&&FAST_DIV_RECIP
		while(qh&&rh<base&&(dlimb_t)qh*(dlimb_t)vn.a[n-2]>((rh<<64)|(dlimb_t)un.a[j+n-2])){
			qh--;
			rh+=vn.a[n-1];
		}
		limb_t qhl=(limb_t)qh;
#else
		while(qh&&rh<base&&(dlimb_t)qh*(dlimb_t)vn.a[n-2]>((rh<<LIMB_BITS)|(dlimb_t)un.a[j+n-2])){
			qh--;
			rh+=vn.a[n-1];
		}
		limb_t qhl=qh;
#endif
		limb_t bor=0,car=0;
		for(int i=0;i<n;i++){
			dlimb_t p=(dlimb_t)vn.a[i]*(dlimb_t)qhl+(dlimb_t)car;
			car=(limb_t)(p>>LIMB_BITS);
			limb_t subtr=(limb_t)p,cur=un.a[j+i];
			dlimb_t t=(dlimb_t)subtr+(dlimb_t)bor;
			un.a[j+i]=(limb_t)((dlimb_t)cur-t);
			bor=(t>(dlimb_t)cur);
		}
		limb_t cur=un.a[j+n];
		dlimb_t t=(dlimb_t)car+(dlimb_t)bor;
		un.a[j+n]=(limb_t)((dlimb_t)cur-t);
		int neg=(t>(dlimb_t)cur);
		q.a[j]=qhl;
		if(neg){
			q.a[j]--;
			dlimb_t c=0;
			for(int i=0;i<n;i++){
				dlimb_t sum=(dlimb_t)un.a[j+i]+(dlimb_t)vn.a[i]+c;
				un.a[j+i]=(limb_t)sum;
				c=sum>>LIMB_BITS;
			}
			un.a[j+n]=(limb_t)((dlimb_t)un.a[j+n]+c);
		}
	}
	nrm(q);
	b rr;
	bi(rr);
	fit(rr,n);
	memcpy(rr.a,un.a,(size_t)n*sizeof(limb_t));
	rr.n=n;
	nrm(rr);
	shr(r,rr,ss);
}

b isq(const b&n){
	b x,t,q;
	bi(x);
	bi(t);
	bi(q);
	int bl=blen(n);
	setu(x,1);
	lshi(x,(bl+1)/2);
	for(;;){
		divq(q,n,x);
		add(t,x,q);
		shr1(t);
		if(cmp(t,x)>=0){
			break;
		}
		cpy(x,t);
	}
	return x;
}

void si(s&x){
	bi(x.v);
	x.s=0;
}

void snrm(s&x){
	nrm(x.v);
	if(!x.v.n){
		x.s=0;
	}
}

void sadd(s&r,const s&a,const s&b2){
	if(!a.s){
		cpy(r.v,b2.v);
		r.s=b2.s;
		return;
	}
	if(!b2.s){
		cpy(r.v,a.v);
		r.s=a.s;
		return;
	}
	if(a.s==b2.s){
		add(r.v,a.v,b2.v);
		r.s=a.s;
		snrm(r);
		return;
	}
	int c=cmp(a.v,b2.v);
	if(!c){
		r.v.n=0;
		r.s=0;
		return;
	}
	if(c>0){
		sub(r.v,a.v,b2.v);
		r.s=a.s;
	}else{
		sub(r.v,b2.v,a.v);
		r.s=b2.s;
	}
	snrm(r);
}

void smul(s&r,const s&a,const b&b2){
	mul(r.v,a.v,b2);
	r.s=a.s;
	snrm(r);
}

void smulb(s&r,const b&a,const s&b2){
	mul(r.v,a,b2.v);
	r.s=b2.s;
	snrm(r);
}

void bs(int a,int b2,b&p,b&q,s&t){
	if(b2-a==1){
		if(!a){
			setu(p,1);
			setu(q,1);
			setu(t.v,13591409);
			t.s=1;
			return;
		}
		uint32_t k=(uint32_t)a;
		uint64_t c3=10939058860032000ULL;
		setu(p,6ull*k-5);
		mul_u32i(p,2*k-1);
		mul_u32i(p,6*k-1);
		setu(q,c3);
		mul_u32i(q,k);
		mul_u32i(q,k);
		mul_u32i(q,k);
		cpy(t.v,p);
		uint64_t mm=13591409ULL+545140134ULL*k;
		mul_u64i(t.v,mm);
		if(k&1){
			t.s=-1;
		}else{
			t.s=1;
		}
		snrm(t);
		return;
	}
	int m=(a+b2)>>1;
	b p1,q1,p2,q2;
	s t1,t2,ta,tb;
	bi(p1);
	bi(q1);
	bi(p2);
	bi(q2);
	si(t1);
	si(t2);
	si(ta);
	si(tb);
	bs(a,m,p1,q1,t1);
	bs(m,b2,p2,q2,t2);
	mul(p,p1,p2);
	mul(q,q1,q2);
	smul(ta,t1,q2);
	smulb(tb,p1,t2);
	sadd(t,ta,tb);
}

uint64_t ts64(const b&x,int p){
#if LIMB64
	int w=p>>6,bb=p&63;
	if(x.n<=w){
		return 0;
	}
	if(!bb){
		return (uint64_t)x.a[w];
	}
	dlimb_t v=(dlimb_t)x.a[w]>>bb;
	if(w+1<x.n){
		v|=(dlimb_t)x.a[w+1]<<(64-bb);
	}
	return (uint64_t)v;
#else
	int w=p>>5,bb=p&31;
	if(x.n<=w){
		return 0;
	}
	if(!bb){
		uint64_t lo=x.a[w],hi=0;
		if(w+1<x.n){
			hi=(uint64_t)x.a[w+1];
		}
		return lo|(hi<<32);
	}
	uint64_t v=(uint64_t)x.a[w]>>bb;
	if(w+1<x.n){
		v|=(uint64_t)x.a[w+1]<<(32-bb);
	}
	if(w+2<x.n){
		v|=(uint64_t)x.a[w+2]<<(64-bb);
	}
	return v;
#endif
}

void w64f(FILE*out,uint64_t v,int w){
	char buf[32];
	for(int i=w-1;i>=0;i--){
		buf[i]=(char)('0'+(v%10));
		v/=10;
	}
	fwrite(buf,1,(size_t)w,out);
}

void w64f18(FILE*out,uint64_t v){
	char buf[18];
	for(int i=17;i>=0;i--){
		buf[i]=(char)('0'+(v%10));
		v/=10;
	}
	fwrite(buf,1,18,out);
}

void shrk(b&y,const b&x,int k){
	if(!x.n){
		y.n=0;
		return;
	}
	if(k<=0){
		cpy(y,x);
		return;
	}
	int w=k/LIMB_BITS,bb=k%LIMB_BITS;
	b t;
	bi(t);
	rshw(t,x,w);
	if(!bb){
		cpy(y,t);
		return;
	}
	shr(y,t,bb);
}

uint64_t p10(int k){
	uint64_t r=1;
	for(int i=0;i<k;i++){
		r*=10;
	}
	return r;
}

uint64_t u64s(const b&x){
#if LIMB64
	if(x.n){
		return (uint64_t)x.a[0];
	}else{
		return 0ULL;
	}
#else
	uint64_t lo=0,hi=0;
	if(x.n>0){
		lo=(uint64_t)x.a[0];
	}
	if(x.n>1){
		hi=(uint64_t)x.a[1];
	}
	return lo|(hi<<32);
#endif
}

pn*bpt(int e){
	pn*n=(pn*)ga.alc(sizeof(pn));
	bi(n->p);
	n->e=e;
	n->l=0;
	n->r=0;
	if(e==1){
		setu(n->p,OUT_BASE);
		return n;
	}
	int m=e/2,h=e-m;
	n->l=bpt(h);
	n->r=bpt(m);
	mul(n->p,n->l->p,n->r->p);
	return n;
}

void emc(pn*n,const b&x,uint64_t*out,int&pos){
	if(n->e==1){
		out[pos]=u64s(x);
		pos++;
		return;
	}
	b q,r;
	bi(q);
	bi(r);
	divm(q,r,x,n->r->p);
	emc(n->l,q,out,pos);
	emc(n->r,r,out,pos);
}

void pfd(FILE*out,const b&fb,int p,int nd){
	if(nd<=0){
		return;
	}
	int grp=(nd+OUT_W-1)/OUT_W,rem=nd%OUT_W,fw=rem?rem:OUT_W;
	pn*rt=bpt(grp);
	b powa;
	bi(powa);
	cpy(powa,rt->p);
	b pow10n;
	bi(pow10n);
	if(fw==OUT_W){
		cpy(pow10n,powa);
	}else{
		b rr;
		bi(rr);
		limb_t dv=(limb_t)p10(OUT_W-fw);
		dms(pow10n,rr,powa,dv);
	}
	b prod;
	bi(prod);
	mul(prod,fb,pow10n);
	b d;
	bi(d);
	shrk(d,prod,p);
	uint64_t*ch=(uint64_t*)ga.alc((size_t)grp*sizeof(uint64_t));
	int pos=0;
	emc(rt,d,ch,pos);
	w64f(out,ch[0],fw);
	for(int i=1;i<grp;i++){
		w64f(out,ch[i],OUT_W);
	}
}

void pfs(FILE*out,b fb,int p,int nd){
#if LIMB64
	uint64_t b18=1000000000000000000ULL;
	int remd=nd%18,grp=nd/18;
	if(remd){
		uint64_t pw=1;
		for(int i=0;i<remd;i++){
			pw*=10;
		}
		mul_u64i(fb,pw);
		uint64_t d=ts64(fb,p);
		truncb(fb,p);
		w64f(out,d,remd);
	}
	for(int i=0;i<grp;i++){
		mul_u64i(fb,b18);
		uint64_t d=ts64(fb,p);
		truncb(fb,p);
		w64f18(out,d);
	}
#else
	uint64_t b9=1000000000ULL;
	int remd=nd%9,grp=nd/9;
	if(remd){
		uint64_t pw=1;
		for(int i=0;i<remd;i++){
			pw*=10;
		}
		mul_u64i(fb,pw);
		uint64_t d=ts64(fb,p);
		truncb(fb,p);
		w64f(out,d,remd);
	}
	for(int i=0;i<grp;i++){
		mul_u64i(fb,b9);
		uint64_t d=ts64(fb,p);
		truncb(fb,p);
		w64f(out,d,9);
	}
#endif
}

int main(){
	setvbuf(stdout,0,_IOFBF,1<<23);
	ga.init();
	int n;
	int ok=scanf("%d",&n);
	if(ok!=1){
		return 0;
	}
	if(n<0){
		n=0;
	}
	ga.rst();
	if(!n){
		fputs("3\n",stdout);
		return 0;
	}
	int g=10,nd=n+g,nn=nd/14+2,p=(int)ceil((nd+1)*3.32192809488736234787)+64;
	b p1,q1,sv,rt,num,den,x,fb,tmp;
	s t;
	bi(p1);
	bi(q1);
	bi(sv);
	bi(rt);
	bi(num);
	bi(den);
	bi(x);
	bi(fb);
	bi(tmp);
	si(t);
	bs(0,nn,p1,q1,t);
	setu(sv,10005);
	lshi(sv,2*p);
	rt=isq(sv);
	mul(tmp,q1,rt);
	cpy(num,tmp);
	mul_u32i(num,426880);
	cpy(den,t.v);
	divq(x,num,den);
	b ip;
	bi(ip);
	shrk(ip,x,p);
	unsigned long long ipu=(unsigned long long)u64s(ip);
	cpy(fb,x);
	truncb(fb,p);
	fprintf(stdout,"%llu.",ipu);
	if(n<OUTPUT_DC_CUT_DIGITS){
		b fc;
		bi(fc);
		cpy(fc,fb);
		pfs(stdout,fc,p,n);
	}else{
		pfd(stdout,fb,p,n);
	}
	fputc('\n',stdout);
	return 0;
}

