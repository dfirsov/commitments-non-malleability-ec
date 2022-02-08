pragma Goals:printall. 
require import SmtMap List Finite FSet CoreMap Int AllCore.

op eq_except_l ['a] (P : 'a -> bool) (m1 m2 : 'a list) : bool =
  forall x, !P x => (x \in m1) <=> (x \in m2).

op sbset ['a 'b]  (m1 m2 : ('a, 'b) fmap) : bool
 = eq_except (fun x => !(x \in m1)) m1 m2.

lemma wtp ['a] : forall (l : 'a list),  uniq l => size l = card (oflist l). 
proof. elim. smt. progress. smt.
qed.

lemma eel1 (P : 'a -> bool) m1 m2 x : eq_except_l P m1 m2 => eq_except_l P (x :: m1) (x :: m2).
smt.
qed.

lemma thm5 ['a 'b]  (m : ('a, 'b) fmap) x : x \in m => exists y, m.[x] = Some y.
smt.
qed.

(* function that checks if fmap does not have duplicates: true = does not have duplicates *)
op up (m : ('a, 'b) fmap) : 'a -> 'b -> bool = (fun (x :'a) (y :'b) => !rng (rem m x) y).
op uniqf ['a 'b]  (m : ('a, 'b) fmap) : bool = filter (up m) m = m.

abbrev (\inp) ['a, 'b] (x : 'a * 'b) (m : ('a, 'b) fmap) : bool = dom m x.`1 /\ m.[x.`1] = Some x.`2.


lemma filterLemma1 (P : ('a -> 'b -> bool)) (m : ('a, 'b) fmap): 
  filter P m = m => (forall x y, m.[x] = Some y => P x y).
proof.
progress. 
smt.  
qed.


lemma filterLemma1' (P : ('a -> 'b -> bool)): forall (m : ('a, 'b) fmap),
  (forall x y, m.[x] = Some y => P x y) => filter P m = m.
proof. 
apply fmapW. progress. 
rewrite -fmap_eqP. progress. smt.
progress.
smt.
qed.


lemma fL (P : ('a -> 'b -> bool)) (m : ('a, 'b) fmap): 
  filter P m = m <=> (forall x y, m.[x] = Some y => P x y).
proof.
smt(filterLemma1 filterLemma1').
qed.


lemma filterLemma2 (m : ('a, 'b) fmap) (P : ('a -> 'b -> bool)): 
  filter P m <> m => (exists x y, m.[x] = Some y => P x y = false).
proof.
progress.
smt. 
qed.


lemma fL2 (m : ('a, 'b) fmap): 
(forall x y, m.[x] = Some y => up m x y) <=>
      uniqf m.
proof.
split. progress.
apply filterLemma1' in H.
rewrite /uniqf. 
smt.
smt.
qed.


lemma uniqfL2 (m : ('a, 'b) fmap): 
   !uniqf m <=> (exists x y, x <> y /\ m.[x] = m.[y] /\ m.[x] <> None).
proof.
split. progress.
rewrite /uniqf/up in H. smt.
progress.
rewrite -domE in H1.  
case(y \notin m). smt.
simplify. move => H2.
rewrite /uniqf/up/rng. 
have ->: (filter (fun (x0 : 'a) (y0 : 'b) => ! (exists (x1 : 'a), (rem m x0).[x1] = Some y0)) m <> m) = (filter (fun (x0 : 'a) (y0 : 'b) => (forall (x1 : 'a), (rem m x0).[x1] <> Some y0)) m <> m).
smt.
have : exists b, m.[x] = Some b. smt.
move => H3.
smt. 
qed.


lemma uniqfL1 (m : ('a, 'b) fmap): 
   (forall x y, x \in m => y \in m => x <> y => m.[x] <> m.[y]) <=> uniqf m.
proof.
split. progress.
rewrite /uniqf/up.
smt.
smt.
qed.


lemma helper (m : ('a, 'b) fmap) (x : 'a) (y : 'b): 
   (x, y) \inp (rem m x) => (x, y) \inp m.
proof.
progress.
smt. smt.
qed.


lemma uniqf_rem (m : ('a, 'b) fmap) (x : 'a): 
   uniqf m => uniqf (rem m x).
proof.
progress.
smt.
qed.


lemma l21 (m : ('a, 'b) fmap): 
(forall x y, m.[x] = Some y => up m x y) =>
      (forall (x : 'a), uniqf (rem m x)).
proof.
progress.
rewrite fL2 in H.
smt. 
qed.


lemma mainl1 : uniqf (empty<: 'a, 'b>) = true.
proof.
rewrite /uniqf.
have ->: (filter (fun (x : 'a) (y : 'b) => ! rng (rem empty x) y) empty) = empty. 
smt.
auto.
qed.


lemma mainl2 (m : ('a, 'b) fmap): 
(forall (x: 'a) (y : 'b), uniqf m.[x <- y]) => 
   (forall (x: 'a) (y: 'b), (uniqf (rem m x) /\ !rng (rem m x) y)).
proof.
progress. 
have : x \in  m.[x <- y].
smt. progress.
have : uniqf m.[x<-y]. smt. 
progress. 
smt.
have : uniqf m.[x<-y]. smt. 
progress.
smt.
qed.


(* function that checks if fmap has duplicates: true = has duplicates *)
op hasdup (m : ('a, 'b) fmap): bool = !uniqf m.

lemma hde : hasdup (empty<: 'a, 'b>) = false.
proof. 
rewrite /hasdup/uniqf. 
smt.
qed.

lemma thm3 ['a 'b] m (c : 'b) (x y : 'a) : !hasdup m => m.[x] = Some c => m.[y] = Some c => x = y.
proof.
rewrite /hasdup.
progress.
rewrite -uniqfL1 in H.
smt. 
qed.

lemma thm4 (m1 m2 : ('a, 'b) fmap) : !hasdup m2 => sbset m1 m2  => !hasdup m1.
proof.
rewrite /hasdup.
progress.
smt. 
qed.

lemma thm11 (m : ('a, 'b) fmap) x c : !hasdup m => x \notin m => hasdup m.[x <- c] = mem (to_seq (rng m)) c.
proof.
progress.
rewrite mem_to_seq.
rewrite finite_rng.
smt. 
qed.

lemma thm6 (m : ('a, 'b) fmap) c c' y : m.[c] = Some y => m.[c'] = Some y => c <> c' => hasdup m.
proof.
progress.
smt. 
qed.


(* domain searching function *)
op solve ['a 'b]  (m : ('a, 'b) fmap) (y : 'b) : 'a list = to_seq (dom (filter (fun (x : 'a) (y' : 'b) => y' = y) m)). 

(* completeness *)
lemma solve1 ['a 'b] (x : 'a) (m : ('a, 'b) fmap) (y : 'b) : m.[x] = Some y => x \in solve m y.
proof.
progress.
rewrite /solve.
case(!dom (filter (fun (_ : 'a) (y' : 'b) => y' = y) m) x). smt.
simplify. progress.
smt.
qed.


(* soundness *)
lemma solve2 ['a 'b] (x : 'a) (m : ('a, 'b) fmap) (y : 'b) : x \in solve m y => m.[x] = Some y.
proof.
progress.
rewrite /solve in H.
have : (x, y) \inp (filter (fun (_ : 'a) (y' : 'b) => y' = y) m). smt. 
move => H1.
smt. 
qed.


lemma thm1 ['a 'b] (x : 'a) m (y : 'b) : !hasdup m => m.[x] = Some y => x \in solve m y => solve m y = [x].
proof.
progress. 
rewrite /hasdup in H. 
rewrite -uniqfL1 in H.
case(x \notin m). smt. simplify. move => H2.
case(m = empty). smt. move => H3.

have : is_finite (dom (filter (fun (_ : 'a) (y' : 'b) => y' = y) m)). 
apply finite_dom. move => h.
have : uniq (to_seq (dom (filter (fun (_ : 'a) (y' : 'b) => y' = y) m))). smt. move => h1.
pose xs := to_seq (dom (filter (fun (_ : 'a) (y' : 'b) => y' = y) m)).

case(xs = []). move => H4.
apply solve1 in H0. rewrite /solve in H0.
smt. move => H4.

case(exists z, xs = [z]).
progress.
case(z=x). progress.
move => H6. 
rewrite /solve in H1.  smt. 
rewrite negb_exists. progress.

case(exists z z1 (zs : 'a list), xs = [z;z1] ++ zs).
progress. 
case(zs = []). move => h2. 
case(z=x). progress. 
have : z1 \in solve m y. rewrite /solve. smt. move => hh.
apply solve2 in hh. smt. move => H7.
have : z \in solve m y. rewrite /solve. smt. move => hh.
apply solve2 in hh. smt. move => H7.
case(z=x). progress. 
have : z1 \in solve m y. rewrite /solve. smt. move => hh.
apply solve2 in hh. smt. move => H8. 
have : z \in xs. smt. move => H9.
apply solve2 in H9. smt.
rewrite negb_exists. 
have ->: (forall (a : 'a), ! (fun (a0 : 'a) => exists (z1 : 'a) (zs : 'a list), xs = a0 :: z1 :: zs) a) = (forall (a : 'a), (fun (a0 : 'a) => forall (z1 : 'a) (zs : 'a list), xs <> a0 :: z1 :: zs) a). smt. progress.
rewrite /solve. have : uniqf m. smt. progress.
rewrite /solve in H1.
have ->: (to_seq (dom (filter (fun (_ : 'a) (y' : 'b) => y' = y) m)) = [x]) = (xs = [x]). smt. 

case(rem x xs = []). smt. progress. 
case(exists x1, x1 \in rem x xs).  
progress.
case(x1=x). smt. progress.
case(x1 \in xs). progress. 

have : dom (filter (fun (_ : 'a) (y' : 'b) => y' = y) m) x1. smt. progress.
case(x1 \in solve m y). smt. progress.
have : m.[x1] <> Some y. smt. progress.  
have : x1 \in to_seq (dom (filter (fun (_ : 'a) (y' : 'b) => y' = y) m)).
  smt. progress. apply solve2 in H15. smt. 
progress. smt. 
rewrite negb_exists. simplify. progress.  
case((rem x xs) = []). smt. progress.
apply mem_eq0 in H9. smt. 
qed.


(* range searching function *)
op lookupc (m : ('a, 'b) fmap) (y : 'b) : bool = (solve m y) <> [].

lemma thm2 (m : ('a,'b) fmap) y : lookupc m y => exists x, m.[x] = Some y.
proof. 
progress. 
rewrite /lookupc/solve in H.
pose xs := to_seq (dom (filter (fun (_ : 'a) (y' : 'b) => y' = y) m)).
have : xs <> []. smt. progress.  
case(exists x, x \in xs). progress. exists x. apply solve2 in H1. 
auto.  
rewrite negb_exists. simplify. progress. 
apply mem_eq0 in H1. smt. 
qed.


lemma thm7 (m : ('a, 'b) fmap) x c c' : !lookupc m c => c <> c' => !lookupc m.[x <- c'] c.
proof.
progress. 
rewrite /lookupc/solve in H.
have : to_seq (dom (filter (fun (_ : 'a) (y' : 'b) => y' = c) m)) = [].
smt. progress.
have : (filter (fun (x : 'a) (y' : 'b) => y' = c) m) = empty. smt. move => H2.
rewrite /lookupc/solve =>//=. 
case(x \notin m). smt. progress.
case(m.[x] = Some c'). smt. move => H4.
case(m.[x] = Some c). smt. move => H5.
smt. 
qed.


lemma thm9 (m : ('a, 'b) fmap) x c : lookupc m.[x <- c] c.
proof.
rewrite /lookupc/solve.
have : x \in to_seq (dom (filter (fun (_ : 'a) (y' : 'b) => y' = c) m.[x <- c])).
smt.  
progress. smt.
qed.

lemma thm10 (m : ('a, 'b) fmap) x : x \in m => lookupc m (oget m.[x]).
proof.
progress. 
pose c := oget m.[x].
rewrite /lookupc.
case(m = empty). smt. move => h.
case(x \in (filter (fun (_ : 'a) (y' : 'b) => y' = c) m)).  
smt. 
smt. 
qed.








