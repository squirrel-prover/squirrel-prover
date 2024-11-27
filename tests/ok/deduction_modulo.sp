include Core.
include WeakSecrecy.

global lemma _ 
  { P : system[pair] } @set:P @equiv:P
  (u : message) b1 b2
:
  Let b = b1 && b2 in
  $( (b, u) |> (if b1 && b2 then u)).
Proof.
  intro *. 
  deduce ~all.
Qed.

global lemma _ 
  { P : system[pair] } @set:P @equiv:P
  (u : message) b1 b2
:
  Let b = b1 && b2 in
  $( (b1 && b2, if b then u) |> (if b1 && b2 then u)).
Proof.
  intro *. 
  deduce ~all.
Qed.

global lemma _ 
  { P : system[pair] } @set:P @equiv:P
  (u : message) b1 b2
:
  Let b = b1 && b2 in
  $( (b1 && b2, if b then u) |> (if b then u)).
Proof.
  intro *. 
  deduce ~all.
Qed.

global lemma _ 
  { P : system[pair] } @set:P @equiv:P
  (u : message) b1 b2
:
  Let b = b1 && b2 in
  $( (b, if b1 && b2 then u) |> (if b1 && b2 then u)).
Proof.
  intro *. 
  deduce ~all.
Qed.

global lemma _ 
  { P : system[pair] } @set:P @equiv:P
  (u : message) b1 b2
:
  Let b = b1 && b2 in
  $( (b, if b1 && b2 then u) |> (if b then u)).
Proof.
  intro *. 
  deduce ~all.
Qed.

global lemma _ 
  { P : system[pair] } @set:P @equiv:P
  (u : message) b1 b2
:
  Let b = b1 && b2 in
  $( (b, if b then u) |> (if b1 && b2 then u)).
Proof.
  intro *. 
  deduce ~all.
Qed.

global lemma _ 
  { P : system[pair] } @set:P @equiv:P
  (u : message) b1 b2
:
  Let b = b1 && b2 in
  $( (b1 && b2, if b1 && b2 then u) |> (if b then u)).
Proof.
  intro *. 
  deduce ~all.
Qed.
