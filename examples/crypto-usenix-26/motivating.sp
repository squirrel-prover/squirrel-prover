include Core.

(* ------------------------------------------------------ *)
(* Declare a number of abstract types for public keys, 
   secret keys, ...
   We assume that these types can be encoded as bit-strings using the
   `serializable` tag. *)

type pkey[serializable]. (* public key *)
type skey[serializable]. (* secret key *)
type rand[serializable]. (* randomness *)


(* ------------------------------------------------------ *)
(* Declare an abstract asymmetric encryption scheme. *)

(* public key generation procedure *)
op pub : skey -> pkey.

(* encryption procedure *)
op enc : message -> rand -> pkey -> message.

(* decryption procedure *)
op dec : message -> skey -> message.

(* ------------------------------------------------------ *)
(* Assume that the encryption scheme satisfies the IND-CCA2 game. *)

game CCA2 = {
  rnd key : skey;
  var log = empty_set;

  oracle pub = {
    return pub key
  }

  oracle left_right m0 m1 = { 
    rnd r : rand;
    var e = enc (diff(m0,m1)) r (pub key);
    log := add e log;
    return (if len m0 = len m1 then e );
  }

  oracle decrypt c = {
    return (if not (mem c log) then dec c key );
  }
}.

(* ------------------------------------------------------ *)
(* Preliminaries definitions. *)

channel c.

(* the secret encryption key is randomly sampled *)
name k : skey.

(* some randomness used by the asymmetric encryption *)
name r : rand.

action V : 0.    (* the `V`oter sends its encrypted ballot to the mixnet *)
action M : 1.    (* the `M`ixnet inputs an encrypted ballot *)
action P : 1.    (* the mixnet `P`ublish the decrypted ballots *)

(* an arbitrary dummy value *)
op dummy : message.

(* serialize a public key as a message (i.e. a bitstring) *)
op format : pkey -> message.

(* Mutable state where the mixnet stores the decrypted ballots. *)
mutable bb (i:index) : message = zero.

(* process mutex used to ensure that there are no 
   race-condition on `bb` *) 
mutex mutex_bb:0.

(* Take an array of bitstrings (represented by the type `message`)
   indexed by `index` (represented as a function from `index` to
   `message`), shuffle it, and serialize it as a `mesasge`. *) 
op shuffle : (index -> message) -> message.

(* ------------------------------------------------------ *)
(* The mixnet process. *)

system MixNet =
  PUB : out(c,format (pub k)) |

 (* the voter `V` sends its encrypted ballot *)
  V: (in(c,x);
      out(c, enc diff(x,dummy) r (pub k))) |

 (* collect and decrypts ballot into `bb` *)
  M: (!_i in(c,y);
          lock mutex_bb;
          bb(i) :=
            if V < M i &&
               y = enc diff(input@V,dummy) r (pub k)
            then input@V
            else dec y k;
          unlock mutex_bb) |

 (* publish `bb` once collection (i.e. sub-processes `M`) are done *)
  P: (lock mutex_bb;
      let BB = fun i => bb i in
      out(c, shuffle BB);
      unlock mutex_bb).


(* ------------------------------------------------------ *)
(* We can prove the equivalence of the left and right components of the
   process `MixNet` directly by reduction to IND-CCA2. 
   This require our improved simulator synthesis procedure, that can
   synthesize a memoizing simulator. *)
global lemma _ @system:MixNet (t:_[adv]) :
  [V <= t] -> [len (input@V) = len dummy] ->
  equiv(frame@t).
Proof.
  intro HA Hlen.
  by crypto
       ~time_sensitive          (* use the improved synthesis procedure *)
       ~no_subgoal_on_failure   (* early failure, to provide a more robust 
                                   proof-script *)
      CCA2                      (* use the `CCA2` game *)
      (key:k).                  (* we manually tell `crypto` to map name 
                                  `k` to `key` in `CCA2` *)
Qed.

(* ------------------------------------------------------ *)
(* Let us see what happens with a less precise invariant,
   i.e. removing the `~time_sensitive` option. *)
global lemma _ @system:MixNet (t:_[adv]) :
  [V<=t] -> [len (input@V) = len dummy] ->
  equiv(frame@t).
Proof.
  intro HA Hlen.
  crypto ~no_subgoal_on_failure CCA2 => //.

  (* We cleanup the proof-goal to make the issue more visible. *)
  intro i [H1 H2] [H1' H2' H3 H4].
  clear H1' H2'. (* duplicates *)
  clear H3. (* vacuous *)

  (* Now, the goal considers a case where `M i` decrypts,
     and requires that `input@M i` is not the encryption produced by `V`.
     This is obvious if `V < M i`. Otherwise it is also true but quite
     technical to prove (we have to show that the attacker could not
     have forged `V`'s output, not knowing `k` and `r`).
     It is also irrelevant because the log should be empty if `M i`
     is executed before `V`: this is where the time sensitive invariant
     helps. *)
Abort.
