(* Rem -> C-x C-+ *)

(* Declaration of a hash function. *)
hash h

(* Declaration of two constants. *)
abstract ok:message
abstract ko:message

(* Declaration of an indexed key, allowing to model one key for each tag *)
name key : index->message

(* Channel names, pretty much useless honnestly. *)
channel cT
channel cR

(* The tag creates a fresh challenge, and outputs it along with a keyed hash. *)
process tag(i:index) =
  new nT;
  out(cT, <nT, h(nT,key(i))>)

(* The reader expects a message whose second component is
   a hash of the first component with a valid key. *)
process reader(j:index) =
  in(cT,x);
  try find i such that snd(x) = h(fst(x),key(i)) in
    out(cR,ok)
  else
    out(cR,ko)

system ((!_j reader(j)) | (!_i !_k tag(i))).

(* There should be some authentication property :
   if the reader outputs ok,
   some tag produced the corresponding message. *)
