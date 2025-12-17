set smtSteps=10000.

channel c
abstract m : message
abstract n : message
abstract f : message -> message
mutable s : message = m.
mutable ho : message->message = f.

mutex ls:0.

process A = 
        lock ls;
	s:=m;
	out(c,s);
        unlock ls.

process B =
        lock ls;
	if s=m then 
		s:=n;
		out(c,s);
                unlock ls 
	else 
		s:=m;
		out(c,s);
                unlock ls.

system !_i (A|B).


lemma state(i:index) : happens(A(i))=>s@A(i)=m.
 Proof. smt. Qed.

lemma state2(i:index) : happens(B(i)) => s@B(i)=n.
Proof. smt. Qed.

lemma state3(i:index) : happens(B1(i)) => s@B1(i)=m.
Proof. smt. Qed.

lemma condA(i:index) : happens(A(i)) => cond@A(i).
Proof. smt. Qed.

lemma condB(i:index) : cond@B(i) => s@pred(B(i))=m.
Proof. smt. Qed.

lemma condB_false(i:index) : happens(B(i)) => cond@B(i).
Proof. checkfail smt exn Failure. Abort.

lemma condB1(i:index) : cond@B1(i) => s@pred(B1(i))<>m.
Proof. smt. Qed.

lemma condB1_false(i:index) : happens(B1(i)) => cond@B1(i).
Proof. checkfail smt exn Failure. Abort.

name k  : message.

let m_let : message = k.

let m2_let x : message = <x,k>.

lemma[any] m_let_value : m_let=k. 
Proof. smt. Qed.

lemma[any] m2_let_value : forall x:message,  m2_let x = <x,k>. 
Proof. smt. Qed.
