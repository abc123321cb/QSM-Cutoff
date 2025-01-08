#include "quorum-leader-election-wo-maj.node_6.finite.h"

#include <sstream>
#include <algorithm>

#include <iostream>
#include <stdlib.h>
#include <sys/types.h>          /* See NOTES */
#include <sys/stat.h>
#include <fcntl.h>
#ifdef _WIN32
#include <winsock2.h>
#include <WS2tcpip.h>
#include <io.h>
#define isatty _isatty
#else
#include <sys/socket.h>
#include <netinet/in.h>
#include <netinet/ip.h> 
#include <sys/select.h>
#include <unistd.h>
#define _open open
#define _dup2 dup2
#endif
#include <string.h>
#include <stdio.h>
#include <string>
#if __cplusplus < 201103L
#else
#include <cstdint>
#endif
typedef quorum_leader_election_wo_maj__node_6__finite ivy_class;
std::ofstream __ivy_out;
std::ofstream __ivy_modelfile;
void __ivy_exit(int code){exit(code);}

class reader {
public:
    virtual int fdes() = 0;
    virtual void read() = 0;
    virtual void bind() {}
    virtual bool running() {return fdes() >= 0;}
    virtual bool background() {return false;}
    virtual ~reader() {}
};

class timer {
public:
    virtual int ms_delay() = 0;
    virtual void timeout(int) = 0;
    virtual ~timer() {}
};

#ifdef _WIN32
DWORD WINAPI ReaderThreadFunction( LPVOID lpParam ) 
{
    reader *cr = (reader *) lpParam;
    cr->bind();
    while (true)
        cr->read();
    return 0;
} 

DWORD WINAPI TimerThreadFunction( LPVOID lpParam ) 
{
    timer *cr = (timer *) lpParam;
    while (true) {
        int ms = cr->ms_delay();
        Sleep(ms);
        cr->timeout(ms);
    }
    return 0;
} 
#else
void * _thread_reader(void *rdr_void) {
    reader *rdr = (reader *) rdr_void;
    rdr->bind();
    while(rdr->running()) {
        rdr->read();
    }
    delete rdr;
    return 0; // just to stop warning
}

void * _thread_timer( void *tmr_void ) 
{
    timer *tmr = (timer *) tmr_void;
    while (true) {
        int ms = tmr->ms_delay();
        struct timespec ts;
        ts.tv_sec = ms/1000;
        ts.tv_nsec = (ms % 1000) * 1000000;
        nanosleep(&ts,NULL);
        tmr->timeout(ms);
    }
    return 0;
} 
#endif 

void quorum_leader_election_wo_maj__node_6__finite::install_reader(reader *r) {
    #ifdef _WIN32

        DWORD dummy;
        HANDLE h = CreateThread( 
            NULL,                   // default security attributes
            0,                      // use default stack size  
            ReaderThreadFunction,   // thread function name
            r,                      // argument to thread function 
            0,                      // use default creation flags 
            &dummy);                // returns the thread identifier 
        if (h == NULL) {
            std::cerr << "failed to create thread" << std::endl;
            exit(1);
        }
        thread_ids.push_back(h);
    #else
        pthread_t thread;
        int res = pthread_create(&thread, NULL, _thread_reader, r);
        if (res) {
            std::cerr << "failed to create thread" << std::endl;
            exit(1);
        }
        thread_ids.push_back(thread);
    #endif
}      

void quorum_leader_election_wo_maj__node_6__finite::install_thread(reader *r) {
    install_reader(r);
}

void quorum_leader_election_wo_maj__node_6__finite::install_timer(timer *r) {
    #ifdef _WIN32

        DWORD dummy;
        HANDLE h = CreateThread( 
            NULL,                   // default security attributes
            0,                      // use default stack size  
            TimersThreadFunction,   // thread function name
            r,                      // argument to thread function 
            0,                      // use default creation flags 
            &dummy);                // returns the thread identifier 
        if (h == NULL) {
            std::cerr << "failed to create thread" << std::endl;
            exit(1);
        }
        thread_ids.push_back(h);
    #else
        pthread_t thread;
        int res = pthread_create(&thread, NULL, _thread_timer, r);
        if (res) {
            std::cerr << "failed to create thread" << std::endl;
            exit(1);
        }
        thread_ids.push_back(thread);
    #endif
}      


#ifdef _WIN32
    void quorum_leader_election_wo_maj__node_6__finite::__lock() { WaitForSingleObject(mutex,INFINITE); }
    void quorum_leader_election_wo_maj__node_6__finite::__unlock() { ReleaseMutex(mutex); }
#else
    void quorum_leader_election_wo_maj__node_6__finite::__lock() { pthread_mutex_lock(&mutex); }
    void quorum_leader_election_wo_maj__node_6__finite::__unlock() { pthread_mutex_unlock(&mutex); }
#endif

/*++
Copyright (c) Microsoft Corporation

This string hash function is borrowed from Microsoft Z3
(https://github.com/Z3Prover/z3). 

--*/


#define mix(a,b,c)              \
{                               \
  a -= b; a -= c; a ^= (c>>13); \
  b -= c; b -= a; b ^= (a<<8);  \
  c -= a; c -= b; c ^= (b>>13); \
  a -= b; a -= c; a ^= (c>>12); \
  b -= c; b -= a; b ^= (a<<16); \
  c -= a; c -= b; c ^= (b>>5);  \
  a -= b; a -= c; a ^= (c>>3);  \
  b -= c; b -= a; b ^= (a<<10); \
  c -= a; c -= b; c ^= (b>>15); \
}

#ifndef __fallthrough
#define __fallthrough
#endif

namespace hash_space {

// I'm using Bob Jenkin's hash function.
// http://burtleburtle.net/bob/hash/doobs.html
unsigned string_hash(const char * str, unsigned length, unsigned init_value) {
    unsigned a, b, c, len;

    /* Set up the internal state */
    len = length;
    a = b = 0x9e3779b9;  /* the golden ratio; an arbitrary value */
    c = init_value;      /* the previous hash value */

    /*---------------------------------------- handle most of the key */
    while (len >= 12) {
        a += reinterpret_cast<const unsigned *>(str)[0];
        b += reinterpret_cast<const unsigned *>(str)[1];
        c += reinterpret_cast<const unsigned *>(str)[2];
        mix(a,b,c);
        str += 12; len -= 12;
    }

    /*------------------------------------- handle the last 11 bytes */
    c += length;
    switch(len) {        /* all the case statements fall through */
    case 11: 
        c+=((unsigned)str[10]<<24);
        __fallthrough;
    case 10: 
        c+=((unsigned)str[9]<<16);
        __fallthrough;
    case 9 : 
        c+=((unsigned)str[8]<<8);
        __fallthrough;
        /* the first byte of c is reserved for the length */
    case 8 : 
        b+=((unsigned)str[7]<<24);
        __fallthrough;
    case 7 : 
        b+=((unsigned)str[6]<<16);
        __fallthrough;
    case 6 : 
        b+=((unsigned)str[5]<<8);
        __fallthrough;
    case 5 : 
        b+=str[4];
        __fallthrough;
    case 4 : 
        a+=((unsigned)str[3]<<24);
        __fallthrough;
    case 3 : 
        a+=((unsigned)str[2]<<16);
        __fallthrough;
    case 2 : 
        a+=((unsigned)str[1]<<8);
        __fallthrough;
    case 1 : 
        a+=str[0];
        __fallthrough;
        /* case 0: nothing left to add */
    }
    mix(a,b,c);
    /*-------------------------------------------- report the result */
    return c;
}

}




struct ivy_value {
    int pos;
    std::string atom;
    std::vector<ivy_value> fields;
    bool is_member() const {
        return atom.size() && fields.size();
    }
};
struct deser_err {
};

struct ivy_ser {
    virtual void  set(long long) = 0;
    virtual void  set(bool) = 0;
    virtual void  setn(long long inp, int len) = 0;
    virtual void  set(const std::string &) = 0;
    virtual void  open_list(int len) = 0;
    virtual void  close_list() = 0;
    virtual void  open_list_elem() = 0;
    virtual void  close_list_elem() = 0;
    virtual void  open_struct() = 0;
    virtual void  close_struct() = 0;
    virtual void  open_field(const std::string &) = 0;
    virtual void  close_field() = 0;
    virtual void  open_tag(int, const std::string &) {throw deser_err();}
    virtual void  close_tag() {}
    virtual ~ivy_ser(){}
};
struct ivy_binary_ser : public ivy_ser {
    std::vector<char> res;
    void setn(long long inp, int len) {
        for (int i = len-1; i >= 0 ; i--)
            res.push_back((inp>>(8*i))&0xff);
    }
    void set(long long inp) {
        setn(inp,sizeof(long long));
    }
    void set(bool inp) {
        set((long long)inp);
    }
    void set(const std::string &inp) {
        for (unsigned i = 0; i < inp.size(); i++)
            res.push_back(inp[i]);
        res.push_back(0);
    }
    void open_list(int len) {
        set((long long)len);
    }
    void close_list() {}
    void open_list_elem() {}
    void close_list_elem() {}
    void open_struct() {}
    void close_struct() {}
    virtual void  open_field(const std::string &) {}
    void close_field() {}
    virtual void  open_tag(int tag, const std::string &) {
        set((long long)tag);
    }
    virtual void  close_tag() {}
};

struct ivy_deser {
    virtual void  get(long long&) = 0;
    virtual void  get(std::string &) = 0;
    virtual void  getn(long long &res, int bytes) = 0;
    virtual void  open_list() = 0;
    virtual void  close_list() = 0;
    virtual bool  open_list_elem() = 0;
    virtual void  close_list_elem() = 0;
    virtual void  open_struct() = 0;
    virtual void  close_struct() = 0;
    virtual void  open_field(const std::string &) = 0;
    virtual void  close_field() = 0;
    virtual int   open_tag(const std::vector<std::string> &) {throw deser_err();}
    virtual void  close_tag() {}
    virtual void  end() = 0;
    virtual ~ivy_deser(){}
};

struct ivy_binary_deser : public ivy_deser {
    std::vector<char> inp;
    int pos;
    std::vector<int> lenstack;
    ivy_binary_deser(const std::vector<char> &inp) : inp(inp),pos(0) {}
    virtual bool more(unsigned bytes) {return inp.size() >= pos + bytes;}
    virtual bool can_end() {return pos == inp.size();}
    void get(long long &res) {
       getn(res,8);
    }
    void getn(long long &res, int bytes) {
        if (!more(bytes))
            throw deser_err();
        res = 0;
        for (int i = 0; i < bytes; i++)
            res = (res << 8) | (((long long)inp[pos++]) & 0xff);
    }
    void get(std::string &res) {
        while (more(1) && inp[pos]) {
//            if (inp[pos] == '"')
//                throw deser_err();
            res.push_back(inp[pos++]);
        }
        if(!(more(1) && inp[pos] == 0))
            throw deser_err();
        pos++;
    }
    void open_list() {
        long long len;
        get(len);
        lenstack.push_back(len);
    }
    void close_list() {
        lenstack.pop_back();
    }
    bool open_list_elem() {
        return lenstack.back();
    }
    void close_list_elem() {
        lenstack.back()--;
    }
    void open_struct() {}
    void close_struct() {}
    virtual void  open_field(const std::string &) {}
    void close_field() {}
    int open_tag(const std::vector<std::string> &tags) {
        long long res;
        get(res);
        if (res >= tags.size())
            throw deser_err();
        return res;
    }
    void end() {
        if (!can_end())
            throw deser_err();
    }
};
struct ivy_socket_deser : public ivy_binary_deser {
      int sock;
    public:
      ivy_socket_deser(int sock, const std::vector<char> &inp)
          : ivy_binary_deser(inp), sock(sock) {}
    virtual bool more(unsigned bytes) {
        while (inp.size() < pos + bytes) {
            int oldsize = inp.size();
            int get = pos + bytes - oldsize;
            get = (get < 1024) ? 1024 : get;
            inp.resize(oldsize + get);
            int newbytes;
	    if ((newbytes = read(sock,&inp[oldsize],get)) < 0)
		 { std::cerr << "recvfrom failed\n"; exit(1); }
            inp.resize(oldsize + newbytes);
            if (newbytes == 0)
                 return false;
        }
        return true;
    }
    virtual bool can_end() {return true;}
};

struct out_of_bounds {
    std::string txt;
    int pos;
    out_of_bounds(int _idx, int pos = 0) : pos(pos){
        std::ostringstream os;
        os << "argument " << _idx+1;
        txt = os.str();
    }
    out_of_bounds(const std::string &s, int pos = 0) : txt(s), pos(pos) {}
};

template <class T> T _arg(std::vector<ivy_value> &args, unsigned idx, long long bound);
template <class T> T __lit(const char *);

template <>
bool _arg<bool>(std::vector<ivy_value> &args, unsigned idx, long long bound) {
    if (!(args[idx].atom == "true" || args[idx].atom == "false") || args[idx].fields.size())
        throw out_of_bounds(idx,args[idx].pos);
    return args[idx].atom == "true";
}

template <>
int _arg<int>(std::vector<ivy_value> &args, unsigned idx, long long bound) {
    std::istringstream s(args[idx].atom.c_str());
    s.unsetf(std::ios::dec);
    s.unsetf(std::ios::hex);
    s.unsetf(std::ios::oct);
    long long res;
    s  >> res;
    // int res = atoi(args[idx].atom.c_str());
    if (bound && (res < 0 || res >= bound) || args[idx].fields.size())
        throw out_of_bounds(idx,args[idx].pos);
    return res;
}

template <>
long long _arg<long long>(std::vector<ivy_value> &args, unsigned idx, long long bound) {
    std::istringstream s(args[idx].atom.c_str());
    s.unsetf(std::ios::dec);
    s.unsetf(std::ios::hex);
    s.unsetf(std::ios::oct);
    long long res;
    s  >> res;
//    long long res = atoll(args[idx].atom.c_str());
    if (bound && (res < 0 || res >= bound) || args[idx].fields.size())
        throw out_of_bounds(idx,args[idx].pos);
    return res;
}

template <>
unsigned long long _arg<unsigned long long>(std::vector<ivy_value> &args, unsigned idx, long long bound) {
    std::istringstream s(args[idx].atom.c_str());
    s.unsetf(std::ios::dec);
    s.unsetf(std::ios::hex);
    s.unsetf(std::ios::oct);
    unsigned long long res;
    s  >> res;
//    unsigned long long res = atoll(args[idx].atom.c_str());
    if (bound && (res < 0 || res >= bound) || args[idx].fields.size())
        throw out_of_bounds(idx,args[idx].pos);
    return res;
}

template <>
unsigned _arg<unsigned>(std::vector<ivy_value> &args, unsigned idx, long long bound) {
    std::istringstream s(args[idx].atom.c_str());
    s.unsetf(std::ios::dec);
    s.unsetf(std::ios::hex);
    s.unsetf(std::ios::oct);
    unsigned res;
    s  >> res;
//    unsigned res = atoll(args[idx].atom.c_str());
    if (bound && (res < 0 || res >= bound) || args[idx].fields.size())
        throw out_of_bounds(idx,args[idx].pos);
    return res;
}


std::ostream &operator <<(std::ostream &s, const __strlit &t){
    s << "\"" << t.c_str() << "\"";
    return s;
}

template <>
__strlit _arg<__strlit>(std::vector<ivy_value> &args, unsigned idx, long long bound) {
    if (args[idx].fields.size())
        throw out_of_bounds(idx,args[idx].pos);
    return args[idx].atom;
}

template <class T> void __ser(ivy_ser &res, const T &inp);

template <>
void __ser<int>(ivy_ser &res, const int &inp) {
    res.set((long long)inp);
}

template <>
void __ser<long long>(ivy_ser &res, const long long &inp) {
    res.set(inp);
}

template <>
void __ser<unsigned long long>(ivy_ser &res, const unsigned long long &inp) {
    res.set((long long)inp);
}

template <>
void __ser<unsigned>(ivy_ser &res, const unsigned &inp) {
    res.set((long long)inp);
}

template <>
void __ser<bool>(ivy_ser &res, const bool &inp) {
    res.set(inp);
}


template <>
void __ser<__strlit>(ivy_ser &res, const __strlit &inp) {
    res.set(inp);
}

template <class T> void __deser(ivy_deser &inp, T &res);

template <>
void __deser<int>(ivy_deser &inp, int &res) {
    long long temp;
    inp.get(temp);
    res = temp;
}

template <>
void __deser<long long>(ivy_deser &inp, long long &res) {
    inp.get(res);
}

template <>
void __deser<unsigned long long>(ivy_deser &inp, unsigned long long &res) {
    long long temp;
    inp.get(temp);
    res = temp;
}

template <>
void __deser<unsigned>(ivy_deser &inp, unsigned &res) {
    long long temp;
    inp.get(temp);
    res = temp;
}

template <>
void __deser<__strlit>(ivy_deser &inp, __strlit &res) {
    inp.get(res);
}

template <>
void __deser<bool>(ivy_deser &inp, bool &res) {
    long long thing;
    inp.get(thing);
    res = thing;
}

void __deser(ivy_deser &inp, std::vector<bool>::reference res) {
    long long thing;
    inp.get(thing);
    res = thing;
}

class gen;

std::ostream &operator <<(std::ostream &s, const quorum_leader_election_wo_maj__node_6__finite::node &t);
template <>
quorum_leader_election_wo_maj__node_6__finite::node _arg<quorum_leader_election_wo_maj__node_6__finite::node>(std::vector<ivy_value> &args, unsigned idx, long long bound);
template <>
void  __ser<quorum_leader_election_wo_maj__node_6__finite::node>(ivy_ser &res, const quorum_leader_election_wo_maj__node_6__finite::node&);
template <>
void  __deser<quorum_leader_election_wo_maj__node_6__finite::node>(ivy_deser &inp, quorum_leader_election_wo_maj__node_6__finite::node &res);
std::ostream &operator <<(std::ostream &s, const quorum_leader_election_wo_maj__node_6__finite::nset &t);
template <>
quorum_leader_election_wo_maj__node_6__finite::nset _arg<quorum_leader_election_wo_maj__node_6__finite::nset>(std::vector<ivy_value> &args, unsigned idx, long long bound);
template <>
void  __ser<quorum_leader_election_wo_maj__node_6__finite::nset>(ivy_ser &res, const quorum_leader_election_wo_maj__node_6__finite::nset&);
template <>
void  __deser<quorum_leader_election_wo_maj__node_6__finite::nset>(ivy_deser &inp, quorum_leader_election_wo_maj__node_6__finite::nset &res);
int quorum_leader_election_wo_maj__node_6__finite::___ivy_choose(int rng,const char *name,int id) {
        return 0;
    }
struct ivy_nondet_except {}; // lauren-yrluo added
void quorum_leader_election_wo_maj__node_6__finite::__init(){
    /** QRM enumerates all satisfying model for reachability **/
    static int qrm_solution_count = 0;
    const int max_qrm_solution_count = 1;
    if (qrm_solution_count == 0){
        bool __tmp0[6][6];
        for (int M = 0; M < 6; M++) {
            for (int N = 0; N < 6; N++) {
                __tmp0[M][N] = false;
            }
        }
        for (int M = 0; M < 6; M++) {
            for (int N = 0; N < 6; N++) {
                voted[N][M] = __tmp0[M][N];
            }
        }
        bool __tmp1[6];
        for (int N = 0; N < 6; N++) {
            __tmp1[N] = false;
        }
        for (int N = 0; N < 6; N++) {
            isleader[N] = __tmp1[N];
        }
        member[0][0] = true;
        member[0][1] = true;
        member[0][2] = true;
        member[0][3] = true;
        member[0][4] = true;
        member[0][5] = true;
        member[0][6] = true;
        member[0][7] = true;
        member[0][8] = true;
        member[0][9] = true;
        member[0][10] = false;
        member[0][11] = false;
        member[0][12] = false;
        member[0][13] = false;
        member[0][14] = false;
        member[1][0] = true;
        member[1][1] = true;
        member[1][2] = true;
        member[1][3] = true;
        member[1][4] = true;
        member[1][5] = true;
        member[1][6] = false;
        member[1][7] = false;
        member[1][8] = false;
        member[1][9] = false;
        member[1][10] = true;
        member[1][11] = true;
        member[1][12] = true;
        member[1][13] = true;
        member[1][14] = false;
        member[2][0] = true;
        member[2][1] = true;
        member[2][2] = true;
        member[2][3] = false;
        member[2][4] = false;
        member[2][5] = false;
        member[2][6] = true;
        member[2][7] = true;
        member[2][8] = true;
        member[2][9] = false;
        member[2][10] = true;
        member[2][11] = true;
        member[2][12] = true;
        member[2][13] = false;
        member[2][14] = true;
        member[3][0] = true;
        member[3][1] = false;
        member[3][2] = false;
        member[3][3] = true;
        member[3][4] = true;
        member[3][5] = false;
        member[3][6] = true;
        member[3][7] = true;
        member[3][8] = false;
        member[3][9] = true;
        member[3][10] = true;
        member[3][11] = true;
        member[3][12] = false;
        member[3][13] = true;
        member[3][14] = true;
        member[4][0] = false;
        member[4][1] = true;
        member[4][2] = false;
        member[4][3] = true;
        member[4][4] = false;
        member[4][5] = true;
        member[4][6] = true;
        member[4][7] = false;
        member[4][8] = true;
        member[4][9] = true;
        member[4][10] = true;
        member[4][11] = false;
        member[4][12] = true;
        member[4][13] = true;
        member[4][14] = true;
        member[5][0] = false;
        member[5][1] = false;
        member[5][2] = true;
        member[5][3] = false;
        member[5][4] = true;
        member[5][5] = true;
        member[5][6] = false;
        member[5][7] = true;
        member[5][8] = true;
        member[5][9] = true;
        member[5][10] = false;
        member[5][11] = true;
        member[5][12] = true;
        member[5][13] = true;
        member[5][14] = true;
        quorum = nset__node0_node1_node4_node5;
    }
    ++ qrm_solution_count;
    if (qrm_solution_count != max_qrm_solution_count)
        throw (ivy_nondet_except());
    else qrm_solution_count = 0;  // reset
}
void quorum_leader_election_wo_maj__node_6__finite::ext__vote(node v, node n){
        int __tmp2;
        __tmp2 = 1;
        for (int M = 0; M < 6; M++) {
            if (!!voted[v][M]) __tmp2 = 0;
        }
        ivy_assume(__tmp2, "quorum-leader-election-wo-maj.node_6.finite.ivy: line 21");
        voted[v][n] = true;
}
void quorum_leader_election_wo_maj__node_6__finite::ext__become_leader(node n, nset s){
        int __tmp3;
        __tmp3 = 1;
        for (int M = 0; M < 6; M++) {
            if (!(!member[M][s] || voted[M][n])) __tmp3 = 0;
        }
        ivy_assume(__tmp3, "quorum-leader-election-wo-maj.node_6.finite.ivy: line 26");
        isleader[n] = true;
        quorum = s;
}
bool quorum_leader_election_wo_maj__node_6__finite::ext__get_member(node n0, nset n1){
    bool qrm_result;
    qrm_result = member[n0][n1];
    return qrm_result;
}
bool quorum_leader_election_wo_maj__node_6__finite::ext__get_bool_member(node n0, nset n1, bool result){
    bool qrm_result;
    qrm_result = (member[n0][n1] == result);
    return qrm_result;
}
quorum_leader_election_wo_maj__node_6__finite::nset quorum_leader_election_wo_maj__node_6__finite::ext__get_quorum(){
    quorum_leader_election_wo_maj__node_6__finite::nset qrm_result;
    qrm_result = quorum;
    return qrm_result;
}
bool quorum_leader_election_wo_maj__node_6__finite::ext__get_bool_quorum(nset result){
    bool qrm_result;
    qrm_result = (quorum == result);
    return qrm_result;
}
bool quorum_leader_election_wo_maj__node_6__finite::ext__get_isleader(node n0){
    bool qrm_result;
    qrm_result = isleader[n0];
    return qrm_result;
}
bool quorum_leader_election_wo_maj__node_6__finite::ext__get_bool_isleader(node n0, bool result){
    bool qrm_result;
    qrm_result = (isleader[n0] == result);
    return qrm_result;
}
bool quorum_leader_election_wo_maj__node_6__finite::ext__get_voted(node n0, node n1){
    bool qrm_result;
    qrm_result = voted[n0][n1];
    return qrm_result;
}
bool quorum_leader_election_wo_maj__node_6__finite::ext__get_bool_voted(node n0, node n1, bool result){
    bool qrm_result;
    qrm_result = (voted[n0][n1] == result);
    return qrm_result;
}
void quorum_leader_election_wo_maj__node_6__finite::__tick(int __timeout){
}
quorum_leader_election_wo_maj__node_6__finite::quorum_leader_election_wo_maj__node_6__finite(){
#ifdef _WIN32
mutex = CreateMutex(NULL,FALSE,NULL);
#else
pthread_mutex_init(&mutex,NULL);
#endif
__lock();
for (node X__0 = (node)0; (int) X__0 < 6; X__0 = (node)(((int)X__0) + 1)) {
isleader[X__0] = (bool)___ivy_choose(0,"init",0);
}
for (node X__0 = (node)0; (int) X__0 < 6; X__0 = (node)(((int)X__0) + 1)) {
    for (node X__1 = (node)0; (int) X__1 < 6; X__1 = (node)(((int)X__1) + 1)) {
voted[X__0][X__1] = (bool)___ivy_choose(0,"init",0);
    }
}
member[0][0] = true;
member[0][1] = true;
member[0][2] = true;
member[0][3] = true;
member[0][4] = true;
member[0][5] = true;
member[0][6] = true;
member[0][7] = true;
member[0][8] = true;
member[0][9] = true;
member[0][10] = false;
member[0][11] = false;
member[0][12] = false;
member[0][13] = false;
member[0][14] = false;
member[1][0] = true;
member[1][1] = true;
member[1][2] = true;
member[1][3] = true;
member[1][4] = true;
member[1][5] = true;
member[1][6] = false;
member[1][7] = false;
member[1][8] = false;
member[1][9] = false;
member[1][10] = true;
member[1][11] = true;
member[1][12] = true;
member[1][13] = true;
member[1][14] = false;
member[2][0] = true;
member[2][1] = true;
member[2][2] = true;
member[2][3] = false;
member[2][4] = false;
member[2][5] = false;
member[2][6] = true;
member[2][7] = true;
member[2][8] = true;
member[2][9] = false;
member[2][10] = true;
member[2][11] = true;
member[2][12] = true;
member[2][13] = false;
member[2][14] = true;
member[3][0] = true;
member[3][1] = false;
member[3][2] = false;
member[3][3] = true;
member[3][4] = true;
member[3][5] = false;
member[3][6] = true;
member[3][7] = true;
member[3][8] = false;
member[3][9] = true;
member[3][10] = true;
member[3][11] = true;
member[3][12] = false;
member[3][13] = true;
member[3][14] = true;
member[4][0] = false;
member[4][1] = true;
member[4][2] = false;
member[4][3] = true;
member[4][4] = false;
member[4][5] = true;
member[4][6] = true;
member[4][7] = false;
member[4][8] = true;
member[4][9] = true;
member[4][10] = true;
member[4][11] = false;
member[4][12] = true;
member[4][13] = true;
member[4][14] = true;
member[5][0] = false;
member[5][1] = false;
member[5][2] = true;
member[5][3] = false;
member[5][4] = true;
member[5][5] = true;
member[5][6] = false;
member[5][7] = true;
member[5][8] = true;
member[5][9] = true;
member[5][10] = false;
member[5][11] = true;
member[5][12] = true;
member[5][13] = true;
member[5][14] = true;
quorum = (nset)___ivy_choose(0,"init",0);
}
quorum_leader_election_wo_maj__node_6__finite::~quorum_leader_election_wo_maj__node_6__finite(){
    __lock(); // otherwise, thread may die holding lock!
    for (unsigned i = 0; i < thread_ids.size(); i++){
#ifdef _WIN32
       // No idea how to cancel a thread on Windows. We just suspend it
       // so it can't cause any harm as we destruct this object.
       SuspendThread(thread_ids[i]);
#else
        pthread_cancel(thread_ids[i]);
        pthread_join(thread_ids[i],NULL);
#endif
    }
    __unlock();
}
std::ostream &operator <<(std::ostream &s, const quorum_leader_election_wo_maj__node_6__finite::node &t){
    if (t == quorum_leader_election_wo_maj__node_6__finite::node0) s<<"node0";
    if (t == quorum_leader_election_wo_maj__node_6__finite::node1) s<<"node1";
    if (t == quorum_leader_election_wo_maj__node_6__finite::node2) s<<"node2";
    if (t == quorum_leader_election_wo_maj__node_6__finite::node3) s<<"node3";
    if (t == quorum_leader_election_wo_maj__node_6__finite::node4) s<<"node4";
    if (t == quorum_leader_election_wo_maj__node_6__finite::node5) s<<"node5";
    return s;
}
template <>
void  __ser<quorum_leader_election_wo_maj__node_6__finite::node>(ivy_ser &res, const quorum_leader_election_wo_maj__node_6__finite::node&t){
    __ser(res,(int)t);
}
std::ostream &operator <<(std::ostream &s, const quorum_leader_election_wo_maj__node_6__finite::nset &t){
    if (t == quorum_leader_election_wo_maj__node_6__finite::nset__node0_node1_node2_node3) s<<"nset__node0_node1_node2_node3";
    if (t == quorum_leader_election_wo_maj__node_6__finite::nset__node0_node1_node2_node4) s<<"nset__node0_node1_node2_node4";
    if (t == quorum_leader_election_wo_maj__node_6__finite::nset__node0_node1_node2_node5) s<<"nset__node0_node1_node2_node5";
    if (t == quorum_leader_election_wo_maj__node_6__finite::nset__node0_node1_node3_node4) s<<"nset__node0_node1_node3_node4";
    if (t == quorum_leader_election_wo_maj__node_6__finite::nset__node0_node1_node3_node5) s<<"nset__node0_node1_node3_node5";
    if (t == quorum_leader_election_wo_maj__node_6__finite::nset__node0_node1_node4_node5) s<<"nset__node0_node1_node4_node5";
    if (t == quorum_leader_election_wo_maj__node_6__finite::nset__node0_node2_node3_node4) s<<"nset__node0_node2_node3_node4";
    if (t == quorum_leader_election_wo_maj__node_6__finite::nset__node0_node2_node3_node5) s<<"nset__node0_node2_node3_node5";
    if (t == quorum_leader_election_wo_maj__node_6__finite::nset__node0_node2_node4_node5) s<<"nset__node0_node2_node4_node5";
    if (t == quorum_leader_election_wo_maj__node_6__finite::nset__node0_node3_node4_node5) s<<"nset__node0_node3_node4_node5";
    if (t == quorum_leader_election_wo_maj__node_6__finite::nset__node1_node2_node3_node4) s<<"nset__node1_node2_node3_node4";
    if (t == quorum_leader_election_wo_maj__node_6__finite::nset__node1_node2_node3_node5) s<<"nset__node1_node2_node3_node5";
    if (t == quorum_leader_election_wo_maj__node_6__finite::nset__node1_node2_node4_node5) s<<"nset__node1_node2_node4_node5";
    if (t == quorum_leader_election_wo_maj__node_6__finite::nset__node1_node3_node4_node5) s<<"nset__node1_node3_node4_node5";
    if (t == quorum_leader_election_wo_maj__node_6__finite::nset__node2_node3_node4_node5) s<<"nset__node2_node3_node4_node5";
    return s;
}
template <>
void  __ser<quorum_leader_election_wo_maj__node_6__finite::nset>(ivy_ser &res, const quorum_leader_election_wo_maj__node_6__finite::nset&t){
    __ser(res,(int)t);
}


int ask_ret(long long bound) {
    int res;
    while(true) {
        __ivy_out << "? ";
        std::cin >> res;
        if (res >= 0 && res < bound) 
            return res;
        std::cerr << "value out of range" << std::endl;
    }
}


    struct ivy_assume_err {};    // lauren-yrluo added

    class quorum_leader_election_wo_maj__node_6__finite_repl : public quorum_leader_election_wo_maj__node_6__finite {

    public:

    virtual void ivy_assert(bool truth,const char *msg){
        if (!truth) {
            __ivy_out << "assertion_failed(\"" << msg << "\")" << std::endl;
            std::cerr << msg << ": error: assertion failed\n";
            
            __ivy_exit(1);
        }
    }
    virtual void ivy_assume(bool truth,const char *msg){
        if (!truth) {
            // __ivy_out << "assumption_failed(\"" << msg << "\")" << std::endl;  // lauren-yrluo modified 
            // std::cerr << msg << ": error: assumption failed\n";                 // lauren-yrluo modified
            
            // __ivy_exit(1);           // lauren-yrluo modified 
            throw (ivy_assume_err());   // lauren-yrluo modified
        }
    }
        quorum_leader_election_wo_maj__node_6__finite_repl() : quorum_leader_election_wo_maj__node_6__finite(){}

    };

// Override methods to implement low-level network service

bool is_white(int c) {
    return (c == ' ' || c == '\t' || c == '\n' || c == '\r');
}

bool is_ident(int c) {
    return c == '_' || c == '.' || (c >= 'A' &&  c <= 'Z')
        || (c >= 'a' &&  c <= 'z')
        || (c >= '0' &&  c <= '9');
}

void skip_white(const std::string& str, int &pos){
    while (pos < str.size() && is_white(str[pos]))
        pos++;
}

struct syntax_error {
    int pos;
    syntax_error(int pos) : pos(pos) {}
};

void throw_syntax(int pos){
    throw syntax_error(pos);
}

std::string get_ident(const std::string& str, int &pos) {
    std::string res = "";
    while (pos < str.size() && is_ident(str[pos])) {
        res.push_back(str[pos]);
        pos++;
    }
    if (res.size() == 0)
        throw_syntax(pos);
    return res;
}

ivy_value parse_value(const std::string& cmd, int &pos) {
    ivy_value res;
    res.pos = pos;
    skip_white(cmd,pos);
    if (pos < cmd.size() && cmd[pos] == '[') {
        while (true) {
            pos++;
            skip_white(cmd,pos);
            if (pos < cmd.size() && cmd[pos] == ']')
                break;
            res.fields.push_back(parse_value(cmd,pos));
            skip_white(cmd,pos);
            if (pos < cmd.size() && cmd[pos] == ']')
                break;
            if (!(pos < cmd.size() && cmd[pos] == ','))
                throw_syntax(pos);
        }
        pos++;
    }
    else if (pos < cmd.size() && cmd[pos] == '{') {
        while (true) {
            ivy_value field;
            pos++;
            skip_white(cmd,pos);
            field.atom = get_ident(cmd,pos);
            skip_white(cmd,pos);
            if (!(pos < cmd.size() && cmd[pos] == ':'))
                 throw_syntax(pos);
            pos++;
            skip_white(cmd,pos);
            field.fields.push_back(parse_value(cmd,pos));
            res.fields.push_back(field);
            skip_white(cmd,pos);
            if (pos < cmd.size() && cmd[pos] == '}')
                break;
            if (!(pos < cmd.size() && cmd[pos] == ','))
                throw_syntax(pos);
        }
        pos++;
    }
    else if (pos < cmd.size() && cmd[pos] == '"') {
        pos++;
        res.atom = "";
        while (pos < cmd.size() && cmd[pos] != '"') {
            char c = cmd[pos++];
            if (c == '\\') {
                if (pos == cmd.size())
                    throw_syntax(pos);
                c = cmd[pos++];
                c = (c == 'n') ? 10 : (c == 'r') ? 13 : (c == 't') ? 9 : c;
            }
            res.atom.push_back(c);
        }
        if(pos == cmd.size())
            throw_syntax(pos);
        pos++;
    }
    else 
        res.atom = get_ident(cmd,pos);
    return res;
}

void parse_command(const std::string &cmd, std::string &action, std::vector<ivy_value> &args) {
    int pos = 0;
    skip_white(cmd,pos);
    action = get_ident(cmd,pos);
    skip_white(cmd,pos);
    if (pos < cmd.size() && cmd[pos] == '(') {
        pos++;
        skip_white(cmd,pos);
        args.push_back(parse_value(cmd,pos));
        while(true) {
            skip_white(cmd,pos);
            if (!(pos < cmd.size() && cmd[pos] == ','))
                break;
            pos++;
            args.push_back(parse_value(cmd,pos));
        }
        if (!(pos < cmd.size() && cmd[pos] == ')'))
            throw_syntax(pos);
        pos++;
    }
    skip_white(cmd,pos);
    if (pos != cmd.size())
        throw_syntax(pos);
}

struct bad_arity {
    std::string action;
    int num;
    bad_arity(std::string &_action, unsigned _num) : action(_action), num(_num) {}
};

void check_arity(std::vector<ivy_value> &args, unsigned num, std::string &action) {
    if (args.size() != num)
        throw bad_arity(action,num);
}

template <>
quorum_leader_election_wo_maj__node_6__finite::node _arg<quorum_leader_election_wo_maj__node_6__finite::node>(std::vector<ivy_value> &args, unsigned idx, long long bound){
    ivy_value &arg = args[idx];
    if (arg.atom.size() == 0 || arg.fields.size() != 0) throw out_of_bounds(idx,arg.pos);
    if(arg.atom == "node0") return quorum_leader_election_wo_maj__node_6__finite::node0;
    if(arg.atom == "node1") return quorum_leader_election_wo_maj__node_6__finite::node1;
    if(arg.atom == "node2") return quorum_leader_election_wo_maj__node_6__finite::node2;
    if(arg.atom == "node3") return quorum_leader_election_wo_maj__node_6__finite::node3;
    if(arg.atom == "node4") return quorum_leader_election_wo_maj__node_6__finite::node4;
    if(arg.atom == "node5") return quorum_leader_election_wo_maj__node_6__finite::node5;
    throw out_of_bounds("bad value: " + arg.atom,arg.pos);
}
template <>
void __deser<quorum_leader_election_wo_maj__node_6__finite::node>(ivy_deser &inp, quorum_leader_election_wo_maj__node_6__finite::node &res){
    int __res;
    __deser(inp,__res);
    res = (quorum_leader_election_wo_maj__node_6__finite::node)__res;
}
template <>
quorum_leader_election_wo_maj__node_6__finite::nset _arg<quorum_leader_election_wo_maj__node_6__finite::nset>(std::vector<ivy_value> &args, unsigned idx, long long bound){
    ivy_value &arg = args[idx];
    if (arg.atom.size() == 0 || arg.fields.size() != 0) throw out_of_bounds(idx,arg.pos);
    if(arg.atom == "nset__node0_node1_node2_node3") return quorum_leader_election_wo_maj__node_6__finite::nset__node0_node1_node2_node3;
    if(arg.atom == "nset__node0_node1_node2_node4") return quorum_leader_election_wo_maj__node_6__finite::nset__node0_node1_node2_node4;
    if(arg.atom == "nset__node0_node1_node2_node5") return quorum_leader_election_wo_maj__node_6__finite::nset__node0_node1_node2_node5;
    if(arg.atom == "nset__node0_node1_node3_node4") return quorum_leader_election_wo_maj__node_6__finite::nset__node0_node1_node3_node4;
    if(arg.atom == "nset__node0_node1_node3_node5") return quorum_leader_election_wo_maj__node_6__finite::nset__node0_node1_node3_node5;
    if(arg.atom == "nset__node0_node1_node4_node5") return quorum_leader_election_wo_maj__node_6__finite::nset__node0_node1_node4_node5;
    if(arg.atom == "nset__node0_node2_node3_node4") return quorum_leader_election_wo_maj__node_6__finite::nset__node0_node2_node3_node4;
    if(arg.atom == "nset__node0_node2_node3_node5") return quorum_leader_election_wo_maj__node_6__finite::nset__node0_node2_node3_node5;
    if(arg.atom == "nset__node0_node2_node4_node5") return quorum_leader_election_wo_maj__node_6__finite::nset__node0_node2_node4_node5;
    if(arg.atom == "nset__node0_node3_node4_node5") return quorum_leader_election_wo_maj__node_6__finite::nset__node0_node3_node4_node5;
    if(arg.atom == "nset__node1_node2_node3_node4") return quorum_leader_election_wo_maj__node_6__finite::nset__node1_node2_node3_node4;
    if(arg.atom == "nset__node1_node2_node3_node5") return quorum_leader_election_wo_maj__node_6__finite::nset__node1_node2_node3_node5;
    if(arg.atom == "nset__node1_node2_node4_node5") return quorum_leader_election_wo_maj__node_6__finite::nset__node1_node2_node4_node5;
    if(arg.atom == "nset__node1_node3_node4_node5") return quorum_leader_election_wo_maj__node_6__finite::nset__node1_node3_node4_node5;
    if(arg.atom == "nset__node2_node3_node4_node5") return quorum_leader_election_wo_maj__node_6__finite::nset__node2_node3_node4_node5;
    throw out_of_bounds("bad value: " + arg.atom,arg.pos);
}
template <>
void __deser<quorum_leader_election_wo_maj__node_6__finite::nset>(ivy_deser &inp, quorum_leader_election_wo_maj__node_6__finite::nset &res){
    int __res;
    __deser(inp,__res);
    res = (quorum_leader_election_wo_maj__node_6__finite::nset)__res;
}


class stdin_reader: public reader {
    std::string buf;
    std::string eof_flag;

public:
    bool eof(){
      return eof_flag.size();
    }
    virtual int fdes(){
        return 0;
    }
    virtual void read() {
        char tmp[257];
        int chars = ::read(0,tmp,256);
        if (chars == 0) {  // EOF
            if (buf.size())
                process(buf);
            eof_flag = "eof";
        }
        tmp[chars] = 0;
        buf += std::string(tmp);
        size_t pos;
        while ((pos = buf.find('\n')) != std::string::npos) {
            std::string line = buf.substr(0,pos+1);
            buf.erase(0,pos+1);
            process(line);
        }
    }
    virtual void process(const std::string &line) {
        __ivy_out << line;
    }
};

class cmd_reader: public stdin_reader {
    int lineno;
public:
    quorum_leader_election_wo_maj__node_6__finite_repl &ivy;    

    cmd_reader(quorum_leader_election_wo_maj__node_6__finite_repl &_ivy) : ivy(_ivy) {
        lineno = 1;
        if (isatty(fdes()))
            __ivy_out << "> "; __ivy_out.flush();
    }

    virtual void process(const std::string &cmd) {
        std::string action;
        std::vector<ivy_value> args;
        try {
            parse_command(cmd,action,args);
            ivy.__lock();

                if (action == "become_leader") {
                    check_arity(args,2,action);
                    ivy.ext__become_leader(_arg<quorum_leader_election_wo_maj__node_6__finite::node>(args,0,6),_arg<quorum_leader_election_wo_maj__node_6__finite::nset>(args,1,15));
                }
                else
    
                if (action == "get_bool_isleader") {
                    check_arity(args,2,action);
                    __ivy_out  << "= " << ivy.ext__get_bool_isleader(_arg<quorum_leader_election_wo_maj__node_6__finite::node>(args,0,6),_arg<bool>(args,1,2)) << std::endl;
                }
                else
    
                if (action == "get_bool_member") {
                    check_arity(args,3,action);
                    __ivy_out  << "= " << ivy.ext__get_bool_member(_arg<quorum_leader_election_wo_maj__node_6__finite::node>(args,0,6),_arg<quorum_leader_election_wo_maj__node_6__finite::nset>(args,1,15),_arg<bool>(args,2,2)) << std::endl;
                }
                else
    
                if (action == "get_bool_quorum") {
                    check_arity(args,1,action);
                    __ivy_out  << "= " << ivy.ext__get_bool_quorum(_arg<quorum_leader_election_wo_maj__node_6__finite::nset>(args,0,15)) << std::endl;
                }
                else
    
                if (action == "get_bool_voted") {
                    check_arity(args,3,action);
                    __ivy_out  << "= " << ivy.ext__get_bool_voted(_arg<quorum_leader_election_wo_maj__node_6__finite::node>(args,0,6),_arg<quorum_leader_election_wo_maj__node_6__finite::node>(args,1,6),_arg<bool>(args,2,2)) << std::endl;
                }
                else
    
                if (action == "get_isleader") {
                    check_arity(args,1,action);
                    __ivy_out  << "= " << ivy.ext__get_isleader(_arg<quorum_leader_election_wo_maj__node_6__finite::node>(args,0,6)) << std::endl;
                }
                else
    
                if (action == "get_member") {
                    check_arity(args,2,action);
                    __ivy_out  << "= " << ivy.ext__get_member(_arg<quorum_leader_election_wo_maj__node_6__finite::node>(args,0,6),_arg<quorum_leader_election_wo_maj__node_6__finite::nset>(args,1,15)) << std::endl;
                }
                else
    
                if (action == "get_quorum") {
                    check_arity(args,0,action);
                    __ivy_out  << "= " << ivy.ext__get_quorum() << std::endl;
                }
                else
    
                if (action == "get_voted") {
                    check_arity(args,2,action);
                    __ivy_out  << "= " << ivy.ext__get_voted(_arg<quorum_leader_election_wo_maj__node_6__finite::node>(args,0,6),_arg<quorum_leader_election_wo_maj__node_6__finite::node>(args,1,6)) << std::endl;
                }
                else
    
                if (action == "vote") {
                    check_arity(args,2,action);
                    ivy.ext__vote(_arg<quorum_leader_election_wo_maj__node_6__finite::node>(args,0,6),_arg<quorum_leader_election_wo_maj__node_6__finite::node>(args,1,6));
                }
                else
    
            {
                std::cerr << "undefined action: " << action << std::endl;
            }
            ivy.__unlock();
        }
        catch (syntax_error& err) {
            ivy.__unlock();
            std::cerr << "line " << lineno << ":" << err.pos << ": syntax error" << std::endl;
        }
        catch (out_of_bounds &err) {
            ivy.__unlock();
            std::cerr << "line " << lineno << ":" << err.pos << ": " << err.txt << " bad value" << std::endl;
        }
        catch (bad_arity &err) {
            ivy.__unlock();
            std::cerr << "action " << err.action << " takes " << err.num  << " input parameters" << std::endl;
        }
        if (isatty(fdes()))
            __ivy_out << "> "; __ivy_out.flush();
        lineno++;
    }
};



int main(int argc, char **argv){
        int test_iters = 100;
        int runs = 1;

    int seed = 1;
    int sleep_ms = 10;
    int final_ms = 0; 
    
    std::vector<char *> pargs; // positional args
    pargs.push_back(argv[0]);
    for (int i = 1; i < argc; i++) {
        std::string arg = argv[i];
        size_t p = arg.find('=');
        if (p == std::string::npos)
            pargs.push_back(argv[i]);
        else {
            std::string param = arg.substr(0,p);
            std::string value = arg.substr(p+1);

            if (param == "out") {
                __ivy_out.open(value.c_str());
                if (!__ivy_out) {
                    std::cerr << "cannot open to write: " << value << std::endl;
                    return 1;
                }
            }
            else if (param == "iters") {
                test_iters = atoi(value.c_str());
            }
            else if (param == "runs") {
                runs = atoi(value.c_str());
            }
            else if (param == "seed") {
                seed = atoi(value.c_str());
            }
            else if (param == "delay") {
                sleep_ms = atoi(value.c_str());
            }
            else if (param == "wait") {
                final_ms = atoi(value.c_str());
            }
            else if (param == "modelfile") {
                __ivy_modelfile.open(value.c_str());
                if (!__ivy_modelfile) {
                    std::cerr << "cannot open to write: " << value << std::endl;
                    return 1;
                }
            }
            else {
                std::cerr << "unknown option: " << param << std::endl;
                return 1;
            }
        }
    }
    srand(seed);
    if (!__ivy_out.is_open())
        __ivy_out.basic_ios<char>::rdbuf(std::cout.rdbuf());
    argc = pargs.size();
    argv = &pargs[0];
    if (argc == 2){
        argc--;
        int fd = _open(argv[argc],0);
        if (fd < 0){
            std::cerr << "cannot open to read: " << argv[argc] << "\n";
            __ivy_exit(1);
        }
        _dup2(fd, 0);
    }
    if (argc != 1){
        std::cerr << "usage: quorum_leader_election_wo_maj__node_6__finite \n";
        __ivy_exit(1);
    }
    std::vector<std::string> args;
    std::vector<ivy_value> arg_values(0);
    for(int i = 1; i < argc;i++){args.push_back(argv[i]);}

#ifdef _WIN32
    // Boilerplate from windows docs

    {
        WORD wVersionRequested;
        WSADATA wsaData;
        int err;

    /* Use the MAKEWORD(lowbyte, highbyte) macro declared in Windef.h */
        wVersionRequested = MAKEWORD(2, 2);

        err = WSAStartup(wVersionRequested, &wsaData);
        if (err != 0) {
            /* Tell the user that we could not find a usable */
            /* Winsock DLL.                                  */
            printf("WSAStartup failed with error: %d\n", err);
            return 1;
        }

    /* Confirm that the WinSock DLL supports 2.2.*/
    /* Note that if the DLL supports versions greater    */
    /* than 2.2 in addition to 2.2, it will still return */
    /* 2.2 in wVersion since that is the version we      */
    /* requested.                                        */

        if (LOBYTE(wsaData.wVersion) != 2 || HIBYTE(wsaData.wVersion) != 2) {
            /* Tell the user that we could not find a usable */
            /* WinSock DLL.                                  */
            printf("Could not find a usable version of Winsock.dll\n");
            WSACleanup();
            return 1;
        }
    }
#endif
    quorum_leader_election_wo_maj__node_6__finite_repl ivy;
    for(unsigned i = 0; i < argc; i++) {ivy.__argv.push_back(argv[i]);}
    ivy.__init();


    ivy.__unlock();

    cmd_reader *cr = new cmd_reader(ivy);

    // The main thread runs the console reader

    while (!cr->eof())
        cr->read();
    return 0;

    return 0;
}

/***********************************************************/
/**                For QRM DFS reachability               **/
/***********************************************************/

#include <vector>
quorum_leader_election_wo_maj__node_6__finite_repl * ivy_exec;
cmd_reader* ivy_exec_cr;
std::ostringstream ivy_exec_stream;

void ivy_exec_init(){
	__ivy_out.basic_ios<char>::rdbuf(ivy_exec_stream.rdbuf());
	ivy_exec = new quorum_leader_election_wo_maj__node_6__finite_repl;
	ivy_exec -> __unlock();
	ivy_exec_cr = new cmd_reader(*ivy_exec);
}

void ivy_exec_set_buffer(std::string buffer_str){
	ivy_exec_stream.str(buffer_str);
}

void ivy_exec_reset_buffer(){
	ivy_exec_stream.str("");
}

std::string ivy_exec_get_buffer(){
	return ivy_exec_stream.str();
}

void ivy_exec_set_state(std::vector<std::string> state_values){
	std::stringstream(state_values[0]) >> ivy_exec -> isleader[0];
	std::stringstream(state_values[1]) >> ivy_exec -> isleader[1];
	std::stringstream(state_values[2]) >> ivy_exec -> isleader[2];
	std::stringstream(state_values[3]) >> ivy_exec -> isleader[3];
	std::stringstream(state_values[4]) >> ivy_exec -> isleader[4];
	std::stringstream(state_values[5]) >> ivy_exec -> isleader[5];
	{
		ivy_value arg; arg.pos = 0; arg.atom = state_values[6];
		std::vector<ivy_value> args; args.push_back(arg);
		ivy_exec -> quorum = _arg<quorum_leader_election_wo_maj__node_6__finite::nset>(args, 0, 0);
	}
	std::stringstream(state_values[7]) >> ivy_exec -> voted[0][0];
	std::stringstream(state_values[8]) >> ivy_exec -> voted[0][1];
	std::stringstream(state_values[9]) >> ivy_exec -> voted[0][2];
	std::stringstream(state_values[10]) >> ivy_exec -> voted[0][3];
	std::stringstream(state_values[11]) >> ivy_exec -> voted[0][4];
	std::stringstream(state_values[12]) >> ivy_exec -> voted[0][5];
	std::stringstream(state_values[13]) >> ivy_exec -> voted[1][0];
	std::stringstream(state_values[14]) >> ivy_exec -> voted[1][1];
	std::stringstream(state_values[15]) >> ivy_exec -> voted[1][2];
	std::stringstream(state_values[16]) >> ivy_exec -> voted[1][3];
	std::stringstream(state_values[17]) >> ivy_exec -> voted[1][4];
	std::stringstream(state_values[18]) >> ivy_exec -> voted[1][5];
	std::stringstream(state_values[19]) >> ivy_exec -> voted[2][0];
	std::stringstream(state_values[20]) >> ivy_exec -> voted[2][1];
	std::stringstream(state_values[21]) >> ivy_exec -> voted[2][2];
	std::stringstream(state_values[22]) >> ivy_exec -> voted[2][3];
	std::stringstream(state_values[23]) >> ivy_exec -> voted[2][4];
	std::stringstream(state_values[24]) >> ivy_exec -> voted[2][5];
	std::stringstream(state_values[25]) >> ivy_exec -> voted[3][0];
	std::stringstream(state_values[26]) >> ivy_exec -> voted[3][1];
	std::stringstream(state_values[27]) >> ivy_exec -> voted[3][2];
	std::stringstream(state_values[28]) >> ivy_exec -> voted[3][3];
	std::stringstream(state_values[29]) >> ivy_exec -> voted[3][4];
	std::stringstream(state_values[30]) >> ivy_exec -> voted[3][5];
	std::stringstream(state_values[31]) >> ivy_exec -> voted[4][0];
	std::stringstream(state_values[32]) >> ivy_exec -> voted[4][1];
	std::stringstream(state_values[33]) >> ivy_exec -> voted[4][2];
	std::stringstream(state_values[34]) >> ivy_exec -> voted[4][3];
	std::stringstream(state_values[35]) >> ivy_exec -> voted[4][4];
	std::stringstream(state_values[36]) >> ivy_exec -> voted[4][5];
	std::stringstream(state_values[37]) >> ivy_exec -> voted[5][0];
	std::stringstream(state_values[38]) >> ivy_exec -> voted[5][1];
	std::stringstream(state_values[39]) >> ivy_exec -> voted[5][2];
	std::stringstream(state_values[40]) >> ivy_exec -> voted[5][3];
	std::stringstream(state_values[41]) >> ivy_exec -> voted[5][4];
	std::stringstream(state_values[42]) >> ivy_exec -> voted[5][5];
}

bool ivy_exec_run_actions(std::vector<std::string> inputs){
	for (int i=0; i<inputs.size(); ++i){
		std::string input = inputs[i];
		if (input == "STOP_PROTOCOL"){
			delete ivy_exec_cr;
			delete ivy_exec;
			return false;
		}
		try {
			ivy_exec_cr->process(input);
		}
		catch (ivy_assume_err & err) {
			ivy_exec -> __unlock();
			return false;
		}
	}
	return true;
}

const int QRM_IVY_ACTION_COMPLETE   = 0;
const int QRM_IVY_ACTION_INCOMPLETE = 1;
const int QRM_IVY_ACTION_FAIL       = 2;

int ivy_exec_run_action(std::string input){
	if (input == "QRM_STOP_PROTOCOL"){
		delete ivy_exec_cr;
		delete ivy_exec;
		return QRM_IVY_ACTION_COMPLETE;
	}
	try {
		if (input == "QRM_INIT_PROTOCOL"){
			ivy_exec -> __init();
			ivy_exec -> __unlock();
		}
		else ivy_exec_cr->process(input);
	}
	catch (ivy_assume_err & err) {
		ivy_exec -> __unlock();
		return QRM_IVY_ACTION_FAIL;
	}
	catch (ivy_nondet_except & except) {
		ivy_exec -> __unlock();
		return QRM_IVY_ACTION_INCOMPLETE;
	}
	return QRM_IVY_ACTION_COMPLETE;
}
