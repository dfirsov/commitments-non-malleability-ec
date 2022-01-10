require import SmtMap List Finite FSet.


lemma wtp ['a] : forall (l : 'a list),  uniq l => size l = card (oflist l). 
proof. elim. smt. progress. smt.
qed.

op eq_except_l ['a] (P : 'a -> bool) (m1 m2 : 'a list) : bool =
  forall x, !P x => (x \in m1) <=> (x \in m2).

lemma eel1 (P : 'a -> bool) m1 m2 x : eq_except_l P m1 m2 => eq_except_l P (x :: m1) (x :: m2).
smt.
qed.


lemma thm5 ['a 'b]  (m : ('a, 'b) fmap) x : x \in m => exists y, m.[x] = Some y.
smt.
qed.

op sbset ['a 'b]  (m1 m2 : ('a, 'b) fmap) : bool
 = eq_except (fun x => !(x \in m1)) m1 m2.

 
(* delcarative specification of a hasdup function *)
op hasdup ['a 'b] : ('a, 'b) fmap -> bool.
axiom thm3 ['a 'b] m (c : 'b) (x y : 'a) : !hasdup m => m.[x] = Some c => m.[y] = Some c => x = y.
axiom thm4 (m1 m2 : ('a, 'b) fmap) : !hasdup m2 => sbset m1 m2  => !hasdup m1.
axiom thm11 (m : ('a, 'b) fmap) x c : !hasdup m => x \notin m => hasdup m.[x <- c] = mem (to_seq (rng m)) c .
axiom thm6 (m : ('a, 'b) fmap) c c' y : m.[c] = Some y => m.[c'] = Some y => c <> c' => hasdup m.
axiom hde : hasdup (empty<: 'a, 'b>) = false.
 
(* declarative specification of a domain searching function *)
op solve ['a 'b]  (m : ('a, 'b) fmap) (x : 'b) : 'a list.
axiom thm1 ['a 'b] (x : 'a) m (y : 'b) : !hasdup m => m.[x] = Some y => solve m y = [x].

(* declarative specification of a range searching function *)
op lookupc : ('a, 'b) fmap -> 'b -> bool.
axiom thm2 (m : ('a,'b) fmap) c : lookupc m c = true => exists x, m.[x] = Some c.
axiom thm7 (m : ('a, 'b) fmap) x c  c' : lookupc m  c = false => c <> c' => lookupc m.[x <- c']  c = false.
axiom thm9 (m : ('a, 'b) fmap) x c : lookupc m.[x <- c]  c = true.
axiom thm10 (m : ('a, 'b) fmap) x : x \in m => lookupc m (oget m.[x]) = true.


