//Taken from Jscoq ! <3
//
//Provides: caml_unix_ll
function caml_unix_ll(s, args) { 
  if (caml_unix_ll.log) joo_global_object.console.warn(s, args); 
  if (caml_unix_ll.trap) throw new Error("unix trap: '"+ s + "' not implemented");
}
caml_unix_ll.log = true;       // whether to log calls
caml_unix_ll.trap = false;     // whether to halt on calls

//Provides: caml_raise_caml_unix_error
//Requires: caml_named_value, caml_raise_with_arg, caml_new_string
function caml_raise_caml_unix_error(msg) {
  var tag = caml_named_value("Unix.caml_unix_error");
  // var util = require('util');
  // console.log(util.inspect(chan, {showHidden: false, depth: null}));
  caml_raise_with_arg (tag, caml_new_string (msg));
}

//Provides: caml_unix_access
//Requires: caml_unix_ll
function caml_unix_access() {
  caml_unix_ll("caml_unix_access", arguments);
  return 0;
}

function caml_unix_realpath() {
  caml_unix_ll("caml_unix_realpath", arguments);
  return 0;
}


//Provides: caml_unix_alarm
//Requires: caml_unix_ll
function caml_unix_alarm() {
  caml_unix_ll("caml_unix_alarm", arguments);
  return 0;
}

//Provides: caml_unix_bind
//Requires: caml_unix_ll
function caml_unix_bind() {
  caml_unix_ll("caml_unix_bind", arguments);
  return 0;
}

//Provides: caml_unix_close
//Requires: caml_unix_ll
function caml_unix_close() {
  caml_unix_ll("caml_unix_close", arguments);
  return 0;
}

//Provides: caml_unix_connect
//Requires: caml_unix_ll
function caml_unix_connect() {
  caml_unix_ll("caml_unix_connect", arguments);
  return 0;
}

//Provides: caml_unix_dup
//Requires: caml_unix_ll
function caml_unix_dup() {
  caml_unix_ll("caml_unix_dup", arguments);
  return 0;
}

//Provides: caml_unix_dup2
//Requires: caml_unix_ll
function caml_unix_dup2() {
  caml_unix_ll("caml_unix_dup2", arguments);
  return 0;
}

//Provides: caml_unix_environment
//Requires: caml_unix_ll
function caml_unix_environment() {
  caml_unix_ll("caml_unix_environment", arguments);
  return 0;
}

//Provides: caml_unix_error_message
//Requires: caml_unix_ll
function caml_unix_error_message() {
  caml_unix_ll("caml_unix_error_message", arguments);
  return 0;
}

//Provides: caml_unix_execve
//Requires: caml_unix_ll
function caml_unix_execve() {
  caml_unix_ll("caml_unix_execve", arguments);
  return 0;
}

//Provides: caml_unix_execvp
//Requires: caml_unix_ll
function caml_unix_execvp() {
  caml_unix_ll("caml_unix_execvp", arguments);
  return 0;
}

//Provides: caml_unix_execvpe
//Requires: caml_unix_ll
function caml_unix_execvpe() {
  caml_unix_ll("caml_unix_execvpe", arguments);
  return 0;
}

//Provides: caml_unix_getcwd
//Requires: caml_unix_ll
function caml_unix_getcwd() {
  caml_unix_ll("caml_unix_getcwd", arguments);
  return 0;
}

//Provides: caml_unix_fork
//Requires: caml_unix_ll
function caml_unix_fork() {
  caml_unix_ll("caml_unix_fork", arguments);
  return 0;
}

//Provides: caml_unix_getpid
//Requires: caml_unix_ll
function caml_unix_getpid() {
  caml_unix_ll("caml_unix_getpid", arguments);
  return 0;
}

//Provides: caml_unix_getpwnam
//Requires: caml_unix_ll
function caml_unix_getpwnam() {
  caml_unix_ll("caml_unix_getpwnam", arguments);
  return 0;
}

//Provides: caml_unix_getsockname
//Requires: caml_unix_ll
function caml_unix_getsockname() {
  caml_unix_ll("caml_unix_getsockname", arguments);
  return 0;
}

//Provides: caml_unix_kill
//Requires: caml_unix_ll
function caml_unix_kill() {
  caml_unix_ll("caml_unix_kill", arguments);
  return 0;
}

//Provides: caml_unix_listen
//Requires: caml_unix_ll
function caml_unix_listen() {
  caml_unix_ll("caml_unix_listen", arguments);
  return 0;
}

//Provides: caml_unix_pipe
//Requires: caml_unix_ll
function caml_unix_pipe() {
  caml_unix_ll("caml_unix_pipe", arguments);
  return 0;
}

//Provides: caml_unix_read
//Requires: caml_unix_ll
function caml_unix_read() {
  caml_unix_ll("caml_unix_read", arguments);
  return 0;
}

//Provides: caml_unix_open
//Requires: caml_unix_ll
function caml_unix_open() {
  caml_unix_ll("caml_unix_open", arguments);
  return 0;
}

//FIXME This is the way it should be done ↓
//Provides: caml_foo
//Requires: caml_string_of_jsstring
//async function caml_foo() {
//  console.warn("Opening:")
//  console.log(arguments[0])
//  let fname = "theories/"+arguments[0]+".sp";
//  let text = await fetch(fname)
//    .then((r) => {
//      if (r.ok) {
//        return r.text();
//      } 
//      else console.error("KO : Bad file name ? "+fname);
//    })
//    .catch((error) => {console.error(error+" : Couldn't load "+arguments[0])})
//  console.log(text);
//  // FIXME This send too late the text to ocaml…
//  return caml_string_of_jsstring(text)
//  //caml_raise_with_string, caml_global_data
//  // caml_raise_with_string (caml_global_data.Sys_error, text);
//}

//Provides: caml_unix_opendir
//Requires: caml_unix_ll
// function caml_unix_opendir(dir) {
//   caml_unix_ll("caml_unix_opendir", arguments);

  // caml_raise_caml_unix_error("opendir", arguments);
  // return [];
// }

//Provides: caml_unix_readdir
//Requires: caml_unix_ll, caml_raise_constant, caml_global_data
// function caml_unix_readdir(dir) {
//   caml_unix_ll("caml_unix_readdir", arguments);

//   // caml_raise_caml_unix_error("readdir", arguments);
//   caml_raise_constant(caml_global_data.End_of_file);
//   return [];
// }

//Provides: caml_unix_closedir
//Requires: caml_unix_ll
// function caml_unix_closedir() {
//   caml_unix_ll("caml_unix_closedir", arguments);
//   return [];
// }

//Provides: caml_unix_select
//Requires: caml_unix_ll
function caml_unix_select() {
  caml_unix_ll("caml_unix_select", arguments);
  return 0;
}

//Provides: caml_unix_set_close_on_exec
//Requires: caml_unix_ll
function caml_unix_set_close_on_exec() {
  caml_unix_ll("caml_unix_set_close_on_exec", arguments);
  return 0;
}

//Provides: caml_unix_set_nonblock
//Requires: caml_unix_ll
function caml_unix_set_nonblock() {
  caml_unix_ll("caml_unix_set_nonblock", arguments);
  return 0;
}

//Provides: caml_unix_sleep
//Requires: caml_unix_ll
function caml_unix_sleep() {
  caml_unix_ll("caml_unix_sleep", arguments);
  return 0;
}

//Provides: caml_unix_socket
//Requires: caml_unix_ll
function caml_unix_socket() {
  caml_unix_ll("caml_unix_socket", arguments);
  return 0;
}

//Provides: caml_unix_string_of_inet_addr
//Requires: caml_unix_ll
function caml_unix_string_of_inet_addr() {
  caml_unix_ll("caml_unix_string_of_inet_addr", arguments);
  return 0;
}

//Provides: caml_unix_times
//Requires: caml_unix_ll
function caml_unix_times() {
  caml_unix_ll("caml_unix_times", arguments);
  return 0;
}

//Provides: caml_unix_wait
//Requires: caml_unix_ll
function caml_unix_wait() {
  caml_unix_ll("caml_unix_wait", arguments);
  return 0;
}

//Provides: caml_unix_waitpid
//Requires: caml_unix_ll
function caml_unix_waitpid() {
  caml_unix_ll("caml_unix_waitpid", arguments);
  return 0;
}

// Provides: caml_unix_accept
// Requires: caml_unix_ll
function caml_unix_accept()                 { caml_unix_ll("caml_unix_accept", arguments); }
// Provides: caml_unix_chdir
// Requires: caml_unix_ll
function caml_unix_chdir()                  { caml_unix_ll("caml_unix_chdir", arguments); }
// Provides: caml_unix_chmod
// Requires: caml_unix_ll
function caml_unix_chmod()                  { caml_unix_ll("caml_unix_chmod", arguments); }
// Provides: caml_unix_chown
// Requires: caml_unix_ll
function caml_unix_chown()                  { caml_unix_ll("caml_unix_chown", arguments); }
// Provides: caml_unix_chroot
// Requires: caml_unix_ll
function caml_unix_chroot()                 { caml_unix_ll("caml_unix_chroot", arguments); }
// Provides: caml_unix_clear_close_on_exec
// Requires: caml_unix_ll
function caml_unix_clear_close_on_exec()    { caml_unix_ll("caml_unix_clear_close_on_exec", arguments); }
// Provides: caml_unix_clear_nonblock
// Requires: caml_unix_ll
function caml_unix_clear_nonblock()         { caml_unix_ll("caml_unix_clear_nonblock", arguments); }
// Provides: caml_unix_environment_unsafe
// Requires: caml_unix_ll
function caml_unix_environment_unsafe()     { caml_unix_ll("caml_unix_environment_unsafe", arguments); }
// Provides: caml_unix_execv
// Requires: caml_unix_ll
function caml_unix_execv()                  { caml_unix_ll("caml_unix_execv", arguments); }
// Provides: caml_unix_fchmod
// Requires: caml_unix_ll
function caml_unix_fchmod()                 { caml_unix_ll("caml_unix_fchmod", arguments); }
// Provides: caml_unix_fchown
// Requires: caml_unix_ll
function caml_unix_fchown()                 { caml_unix_ll("caml_unix_fchown", arguments); }
// Provides: caml_unix_fstat
// Requires: caml_unix_ll
function caml_unix_fstat()                 { caml_unix_ll("caml_unix_fstat", arguments); }
// Provides: caml_unix_fstat_64
// Requires: caml_unix_ll
function caml_unix_fstat_64()              { caml_unix_ll("caml_unix_fstat_64", arguments); }
// Provides: caml_unix_ftruncate
// Requires: caml_unix_ll
function caml_unix_ftruncate()             { caml_unix_ll("caml_unix_ftruncate", arguments); }
// Provides: caml_unix_ftruncate_64
// Requires: caml_unix_ll
function caml_unix_ftruncate_64()          { caml_unix_ll("caml_unix_ftruncate_64", arguments); }
// Provides: caml_unix_getaddrinfo
// Requires: caml_unix_ll
function caml_unix_getaddrinfo()           { caml_unix_ll("caml_unix_getaddrinfo", arguments); }
// Provides: caml_unix_getegid
// Requires: caml_unix_ll
function caml_unix_getegid()               { caml_unix_ll("caml_unix_getegid", arguments); }
// Provides: caml_unix_geteuid
// Requires: caml_unix_ll
function caml_unix_geteuid()               { caml_unix_ll("caml_unix_geteuid", arguments); }
// Provides: caml_unix_getgid
// Requires: caml_unix_ll
function caml_unix_getgid()                { caml_unix_ll("caml_unix_getgid", arguments); }
// Provides: caml_unix_getgrgid
// Requires: caml_unix_ll
function caml_unix_getgrgid()              { caml_unix_ll("caml_unix_getgrgid", arguments); }
// Provides: caml_unix_getgrnam
// Requires: caml_unix_ll
function caml_unix_getgrnam()              { caml_unix_ll("caml_unix_getgrnam", arguments); }
// Provides: caml_unix_getgroups
// Requires: caml_unix_ll
function caml_unix_getgroups()             { caml_unix_ll("caml_unix_getgroups", arguments); }
// Provides: caml_unix_gethostbyaddr
// Requires: caml_unix_ll
function caml_unix_gethostbyaddr()         { caml_unix_ll("caml_unix_gethostbyaddr", arguments); }
// Provides: caml_unix_gethostbyname
// Requires: caml_unix_ll
function caml_unix_gethostbyname()         { caml_unix_ll("caml_unix_gethostbyname", arguments); }
// Provides: caml_unix_gethostname
// Requires: caml_unix_ll
function caml_unix_gethostname()           { caml_unix_ll("caml_unix_gethostname", arguments); }
// Provides: caml_unix_getitimer
// Requires: caml_unix_ll
function caml_unix_getitimer()             { caml_unix_ll("caml_unix_getitimer", arguments); }
// Provides: caml_unix_getlogin
// Requires: caml_unix_ll
function caml_unix_getlogin()              { caml_unix_ll("caml_unix_getlogin", arguments); }
// Provides: caml_unix_getnameinfo
// Requires: caml_unix_ll
function caml_unix_getnameinfo()           { caml_unix_ll("caml_unix_getnameinfo", arguments); }
// Provides: caml_unix_getpeername
// Requires: caml_unix_ll
function caml_unix_getpeername()           { caml_unix_ll("caml_unix_getpeername", arguments); }
// Provides: caml_unix_getppid
// Requires: caml_unix_ll
function caml_unix_getppid()               { caml_unix_ll("caml_unix_getppid", arguments); }
// Provides: caml_unix_getprotobyname
// Requires: caml_unix_ll
function caml_unix_getprotobyname()        { caml_unix_ll("caml_unix_getprotobyname", arguments); }
// Provides: caml_unix_getprotobynumber
// Requires: caml_unix_ll
function caml_unix_getprotobynumber()      { caml_unix_ll("caml_unix_getprotobynumber", arguments); }
// Provides: caml_unix_getservbyname
// Requires: caml_unix_ll
function caml_unix_getservbyname()         { caml_unix_ll("caml_unix_getservbyname", arguments); }
// Provides: caml_unix_getservbyport
// Requires: caml_unix_ll
function caml_unix_getservbyport()         { caml_unix_ll("caml_unix_getservbyport", arguments); }
// Provides: caml_unix_getsockopt
// Requires: caml_unix_ll
function caml_unix_getsockopt()            { caml_unix_ll("caml_unix_getsockopt", arguments); }
// Provides: caml_unix_initgroups
// Requires: caml_unix_ll
function caml_unix_initgroups()            { caml_unix_ll("caml_unix_initgroups", arguments); }
// Provides: caml_unix_link
// Requires: caml_unix_ll
function caml_unix_link()                  { caml_unix_ll("caml_unix_link", arguments); }
// Provides: caml_unix_lockf
// Requires: caml_unix_ll
function caml_unix_lockf()                 { caml_unix_ll("caml_unix_lockf", arguments); }
// Provides: caml_unix_lseek
// Requires: caml_unix_ll
function caml_unix_lseek()                 { caml_unix_ll("caml_unix_lseek", arguments); }
// Provides: caml_unix_lseek_64
// Requires: caml_unix_ll
function caml_unix_lseek_64()              { caml_unix_ll("caml_unix_lseek_64", arguments); }
// Provides: caml_unix_mkfifo
// Requires: caml_unix_ll
function caml_unix_mkfifo()                { caml_unix_ll("caml_unix_mkfifo", arguments); }
// Provides: caml_unix_nice
// Requires: caml_unix_ll
function caml_unix_nice()                  { caml_unix_ll("caml_unix_nice", arguments); }
// Provides: caml_unix_putenv
// Requires: caml_unix_ll
function caml_unix_putenv()                { caml_unix_ll("caml_unix_putenv", arguments); }
// Provides: caml_unix_recv
// Requires: caml_unix_ll
function caml_unix_recv()                  { caml_unix_ll("caml_unix_recv", arguments); }
// Provides: caml_unix_recvfrom
// Requires: caml_unix_ll
function caml_unix_recvfrom()              { caml_unix_ll("caml_unix_recvfrom", arguments); }
// Provides: caml_unix_rename
// Requires: caml_unix_ll
function caml_unix_rename()                { caml_unix_ll("caml_unix_rename", arguments); }
// Provides: caml_unix_rewinddir
// Requires: caml_unix_ll
// function caml_unix_rewinddir()             { caml_unix_ll("caml_unix_rewinddir", arguments); }
// Provides: caml_unix_send
// Requires: caml_unix_ll
function caml_unix_send()                  { caml_unix_ll("caml_unix_send", arguments); }
// Provides: caml_unix_sendto
// Requires: caml_unix_ll
function caml_unix_sendto()                { caml_unix_ll("caml_unix_sendto", arguments); }
// Provides: caml_unix_setgid
// Requires: caml_unix_ll
function caml_unix_setgid()                { caml_unix_ll("caml_unix_setgid", arguments); }
// Provides: caml_unix_setgroups
// Requires: caml_unix_ll
function caml_unix_setgroups()             { caml_unix_ll("caml_unix_setgroups", arguments); }
// Provides: caml_unix_setitimer
// Requires: caml_unix_ll
function caml_unix_setitimer()             { caml_unix_ll("caml_unix_setitimer", arguments); }
// Provides: caml_unix_setsid
// Requires: caml_unix_ll
function caml_unix_setsid()                { caml_unix_ll("caml_unix_setsid", arguments); }
// Provides: caml_unix_setsockopt
// Requires: caml_unix_ll
function caml_unix_setsockopt()            { caml_unix_ll("caml_unix_setsockopt", arguments); }
// Provides: caml_unix_setuid
// Requires: caml_unix_ll
function caml_unix_setuid()                { caml_unix_ll("caml_unix_setuid", arguments); }
// Provides: caml_unix_shutdown
// Requires: caml_unix_ll
function caml_unix_shutdown()              { caml_unix_ll("caml_unix_shutdown", arguments); }
// Provides: caml_unix_sigpending
// Requires: caml_unix_ll
function caml_unix_sigpending()            { caml_unix_ll("caml_unix_sigpending", arguments); }
// Provides: caml_unix_sigprocmask
// Requires: caml_unix_ll
function caml_unix_sigprocmask()           { caml_unix_ll("caml_unix_sigprocmask", arguments); }
// Provides: caml_unix_sigsuspend
// Requires: caml_unix_ll
function caml_unix_sigsuspend()            { caml_unix_ll("caml_unix_sigsuspend", arguments); }
// Provides: caml_unix_single_write
// Requires: caml_unix_ll
function caml_unix_single_write()          { caml_unix_ll("caml_unix_single_write", arguments); }
// Provides: caml_unix_socketpair
// Requires: caml_unix_ll
function caml_unix_socketpair()            { caml_unix_ll("caml_unix_socketpair", arguments); }
// Provides: caml_unix_tcdrain
// Requires: caml_unix_ll
function caml_unix_tcdrain()               { caml_unix_ll("caml_unix_tcdrain", arguments); }
// Provides: caml_unix_tcflow
// Requires: caml_unix_ll
function caml_unix_tcflow()                { caml_unix_ll("caml_unix_tcflow", arguments); }
// Provides: caml_unix_tcflush
// Requires: caml_unix_ll
function caml_unix_tcflush()               { caml_unix_ll("caml_unix_tcflush", arguments); }
// Provides: caml_unix_tcgetattr
// Requires: caml_unix_ll
function caml_unix_tcgetattr()             { caml_unix_ll("caml_unix_tcgetattr", arguments); }
// Provides: caml_unix_tcsendbreak
// Requires: caml_unix_ll
function caml_unix_tcsendbreak()           { caml_unix_ll("caml_unix_tcsendbreak", arguments); }
// Provides: caml_unix_tcsetattr
// Requires: caml_unix_ll
function caml_unix_tcsetattr()             { caml_unix_ll("caml_unix_tcsetattr", arguments); }
// Provides: caml_unix_truncate
// Requires: caml_unix_ll
function caml_unix_truncate()              { caml_unix_ll("caml_unix_truncate", arguments); }
// Provides: caml_unix_truncate_64
// Requires: caml_unix_ll
function caml_unix_truncate_64()           { caml_unix_ll("caml_unix_truncate_64", arguments); }
// Provides: caml_unix_umask
// Requires: caml_unix_ll
function caml_unix_umask()                 { caml_unix_ll("caml_unix_umask", arguments); }
// Provides: caml_unix_utimes
// Requires: caml_unix_ll
function caml_unix_utimes()                { caml_unix_ll("caml_unix_utimes", arguments); }
// Provides: caml_unix_write
// Requires: caml_unix_ll
function caml_unix_write()                 { caml_unix_ll("caml_unix_write", arguments); }
// Provides: caml_unix_exit
// Requires: caml_unix_ll
function caml_unix_exit()                  { caml_unix_ll("caml_unix_exit", arguments); }
// Provides: caml_unix_spawn
// Requires: caml_unix_ll
function caml_unix_spawn()                 { caml_unix_ll("caml_unix_spawn", arguments); }
// Provides: caml_unix_fsync
// Requires: caml_unix_ll
function caml_unix_fsync()                 { caml_unix_ll("caml_unix_fsync", arguments); }
// Provides: caml_unix_inchannel_of_filedescr
// Requires: caml_unix_ll
function caml_unix_inchannel_of_filedescr()  { caml_unix_ll("caml_unix_inchannel_of_filedescr", arguments); }
// Provides: caml_unix_outchannel_of_filedescr
// Requires: caml_unix_ll
function caml_unix_outchannel_of_filedescr() { caml_unix_ll("caml_unix_outchannel_of_filedescr", arguments); }
// Provides: caml_mutex_try_lock
// Requires: caml_unix_ll
function caml_mutex_try_lock()       { caml_unix_ll("caml_mutex_try_lock", arguments); }
// Provides: caml_thread_join
// Requires: caml_unix_ll
function caml_thread_join()          { caml_unix_ll("caml_thread_join", arguments); }
// Provides: caml_thread_sigmask
// Requires: caml_unix_ll
function caml_thread_sigmask()       { caml_unix_ll("caml_thread_sigmask", arguments); }
// Provides: caml_unix_map_file_bytecode
// Requires: caml_unix_ll
function caml_unix_map_file_bytecode() { caml_unix_ll("caml_unix_map_file_bytecode", arguments); }
// Provides: caml_wait_signal
// Requires: caml_unix_ll
function caml_wait_signal()          { caml_unix_ll("caml_wait_signal", arguments); }
