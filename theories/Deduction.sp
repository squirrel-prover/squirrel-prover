include Logic.
include DeductionSyntax.

global lemma [set: Empty; equiv:Empty] 
  _ ['a 'b 'c] (u : 'b, v : 'a -> 'c) : 
  Let u0 = fun _ => u in
  $(u0 |1> (fun x => v x)) ->
  $(u  |>  (fun x => v x)).
Proof.
  intro u0 H.
  rewrite /(|>).
  rewrite /(|1>) in H.
  destruct H as [f H].
  exists (fun u x => f u) => /=. 
  apply fun_ext => x /=.
  rewrite /u0 /= in H.
  apply H.
Qed.

(* 
# Reasoning rules on Deduction
*)

(* ------------------------------------------------------------------- *)
namespace Classic.
  (* `frame@t ▷ {frame@t' | ∀ t' ≤ t}` *)
  global axiom frame_from_frame {P : system} @set:P : 
    $( (fun t => frame@t) 
       |1> 
       (fun t t' => if t' <= t then frame@t')
    ).
  hint deduce frame_from_frame.

  (* `frame@t ▷ {exec@t' | ∀ t' ≤ t}` *)
  global axiom exec_from_frame {P : system} @set:P : 
    $( (fun t => frame@t) 
       |1> 
       (fun t t' => if t' <= t then exec@t' else witness)
    ).
  hint deduce exec_from_frame.

  (* `frame@t ▷ {output@t' | ∀ t' ≤ t, exec@t'}` *)
  global axiom output_from_frame {P : system} @set:P :
    $( (fun t => frame@t) 
       |1> 
       (fun t t' => if t' <= t && exec@t' then output@t')
    ).
  hint deduce output_from_frame.

  (* `frame@t ▷ {input@t' | ∀ t' < t}` *)
  global axiom input_from_frame {P : system} @set:P : 
    $( (fun t => frame@t) 
       |1> 
       (fun t t' => if pred t' <= t then input@t')
    ).
  hint deduce input_from_frame.
end Classic.

(* ------------------------------------------------------------------- *)

namespace Quantum.
  close Classic.

  (* `frame@t ▷ {exec@t' | ∀ t' ≤ t}` *)
  global axiom exec_from_frame {P : system} @set:P :
    $( (fun t => frame@t)
       |1>
       (fun t t' => if t' <= t then exec@t' else witness)
    ). 
  hint deduce exec_from_frame.

  (* `frame@t ▷ {output@t' | ∀ t' ≤ t, exec@t'}` *)
  global axiom output_from_frame {P : system} @set:P :
    $( (fun t => frame@t)
       |1>
       (fun t t' => if t' <= t && exec@t' then output@t')
    ).
  hint deduce output_from_frame.

  (* `frame@t ▷ {input@t' | ∀ t' < t}` *)
  global axiom input_from_frame {P : system} @set:P :
    $( (fun t => frame@t)
       |1>
       (fun t t' => if pred t' <= t then input@t')
    ).
  hint deduce input_from_frame.

  (* `frame@t ▷ {transcript@t' | ∀ t' < t}` *)
  global axiom transcript_from_frame {P : system} @set:P :
    $( (fun t => frame@t)
       |1>
       (fun t t' => if t' <= t then transcript@t')
    ).
  hint deduce transcript_from_frame.

  (* ------------------------------------------------------------------- *)
  (* `transcript@t ▷ {transcript@t' | ∀ t' < t}` *)
  global axiom transcript_from_transcript {P : system} @set:P :
    $( (fun t => transcript@t)
       |1>
       (fun t t' => if t' <= t then transcript@t')
    ).
  hint deduce transcript_from_transcript.

  (* `transcript@t ▷ {exec@t' | ∀ t' ≤ t}` *)
  global axiom exec_from_transcript {P : system} @set:P :
    $( (fun t => transcript@t)
       |1>
       (fun t t' => if t' <= t then exec@t' else witness)
    ).
  hint deduce exec_from_transcript.

  (* `transcript@t ▷ {output@t' | ∀ t' ≤ t, exec@t'}` *)
  global axiom output_from_transcript {P : system} @set:P :
    $( (fun t => transcript@t)
       |1>
       (fun t t' => if t' <= t && exec@t' then output@t')
    ).
  hint deduce output_from_transcript.

  (* `transcript@t ▷ {input@t' | ∀ t' < t}` *)
  global axiom input_from_transcript {P : system} @set:P :
    $( (fun t => transcript@t)
       |1>
       (fun t t' => if pred t' <= t then input@t')
    ).
  hint deduce input_from_transcript.
end Quantum.
