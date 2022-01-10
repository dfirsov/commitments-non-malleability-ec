pragma Goals:printall.
require import AllCore Distr.
require import HelperFuns.

type in_t, out_t, dup_t, hit_t.
op dout: out_t distr.

module type POracle = {
  proc o(x : in_t): out_t
}.

type d_in_t.
module type Distinguisher (H : POracle) = {
  proc run(_ : d_in_t): out_t
}.


module type Oracle = {
  proc init()      : unit
  proc o(x : in_t) : out_t
}.


theory Lazy.
require import SmtMap.

module LRO : Oracle = {
  var m : (in_t, out_t) fmap

  proc init() = {
    m <- empty;
  }

  proc o(x : in_t) = {
    var r;

    r <$ dout;
    if (x \notin m) {
      m.[x] <- r;
    }
    return oget m.[x];
  }
}.

end Lazy.

abstract theory ListLog.
require import Int List.

op qH : int.

module Log (O : Oracle) = {
  var qs : in_t list

  proc init(): unit = {
          O.init();
    qs <- [];
  }

  proc o(x : in_t): out_t = {
    var r;

    r  <@ O.o(x);
    qs <- x :: qs;
    return r;
  }
}.


end ListLog.


abstract theory ROM_BadCall.
require import List SmtMap.

op qH : int.

clone export ListLog with
  op qH <- qH.

import Lazy.

module type Dist (H : Oracle) = {
  proc a1(x : d_in_t): in_t {H.o}
  proc a2(x : out_t) : out_t {H.o}
  proc a3(_ : out_t) : bool {H.o}
}.


theory OnBound.


op P : glob LRO -> glob Log  -> bool = fun (x : glob LRO) y => (!hasdup x) /\ size y <= qH.
op P' : glob LRO -> glob Log  -> bool = fun (x : glob LRO) y => (!hasdup x) /\ 1 + size y <= qH.


module G0 (D : Dist) (H : Oracle) = {
  var y : out_t
  var z : out_t
  var mm : (in_t, out_t) fmap
  proc main(i : d_in_t): bool = {
    var x,r;
    z <- witness;
    mm <- empty;
         Log(H).init();
    x <@ D(Log(H)).a1(i);
    y <@ Log(H).o(x);
    z <@ D(Log(H)).a2(y);
    mm <- LRO.m; 
    r <@ D(Log(H)).a3(z);
    return r /\ (P LRO.m Log.qs) /\ y <> z;
  }
}.


module G_bad (D : Dist) (H : Oracle) = {
  var mqs : in_t list
  var x : in_t
  proc main(i : d_in_t): bool = {
    var y, z;
    z <- witness;
         Log(H).init();
    x <@ D(Log(H)).a1(i);
    (* Log.qs <- x :: Log.qs; *)
    y <$ dout;
    z <@ D(Log(H)).a2(y);
    LRO.m <- LRO.m.[x <- y];
    mqs <- Log.qs;
    D(Log(H)).a3(z);
    return (x \in mqs) ;
  }
}.



module G1' (D : Dist) (H : Oracle) = {
  var x : in_t
  var y : out_t
  var z : out_t
  var mm : (in_t, out_t) fmap
  proc main(i) = {
    var r;
    mm <- empty;
    z <- witness;
         Log(H).init();
    x <@ D(Log(H)).a1(i);
    y <$ dout ;
    z <@ D(Log(H)).a2(y);
    G1'.mm <- LRO.m;
    LRO.m <- LRO.m.[x <- y];
    G_bad.mqs <- Log.qs;
    r <@ D(Log(H)).a3(z);
    return r /\ (P' LRO.m Log.qs) /\ y <> z /\ G1'.mm.[x] = None;
  }
}.


section.
declare module D : Dist {G1', G0, G_bad }.
axiom D_a1_ll (H <: Oracle { D }): islossless H.o => islossless D(H).a1.
axiom D_a2_ll (H <: Oracle { D }): islossless H.o => islossless D(H).a2.
axiom D_a3_ll (H <: Oracle { D }): islossless H.o => islossless D(H).a3.

axiom dout_ll1  : is_lossless dout.
axiom dout_ll2  : is_uniform dout.


lemma ROM_BadCall &m i  :
     Pr[G0(D,LRO).main(i) @ &m: res]
     <= Pr[G1'(D,LRO).main(i) @ &m: res]
      + Pr[G_bad(D,LRO).main(i) @ &m: res].
proof.
have ->: Pr[G_bad(D,LRO).main(i) @ &m: res] = Pr[G1'(D,LRO).main(i) @ &m: G1'.x \in G_bad.mqs].
+ byequiv (_: ={glob D, arg}  ==> res{1} = (mem G_bad.mqs G1'.x){2})=> //.
  proc.
  call (_: ={glob Log, glob LRO}); first by sim. wp.
call (_: ={glob Log, glob LRO}); first by sim.
  rnd;wp;call (_: ={glob Log, glob LRO}); first by sim.
  inline *. wp. skip. progress.
have: Pr[G0(D,LRO).main(i) @ &m: res] <= Pr[G1'(D,LRO).main(i) @ &m: res \/ G1'.x \in G_bad.mqs].
+ byequiv (_: ={glob D, arg}  ==> (!G1'.x \in G_bad.mqs){2} => ={res})=> //; last by smt().
  proc.
seq 2 2 : (={glob D, i}
  /\ G0.z{1} = G1'.z{2}
  /\ G0.mm{1} = G1'.mm{2}
  /\ (G1'.mm = empty){2}). wp.  skip. progress.
  seq 2 2 : ( ={glob D, glob Log, glob LRO}
  /\ x{1} = G1'.x{2} /\ (! (G1'.x{2} \in Log.qs{2}) => x{1}  = G1'.x{2}
        /\ G0.z{1} = G1'.z{2}
        /\ G0.mm{1} = G1'.mm{2}
        /\ (G1'.mm = empty){2}
        /\ (forall x, x \in Log.qs{2} = x \in LRO.m{2})
        /\ (forall x, x \in Log.qs{1} = x \in LRO.m{1}))).
inline*. sp. wp. call (_: ={glob LRO, glob Log} /\ 
  (forall x, x \in Log.qs{2} = x \in LRO.m{2}) /\ (forall x, x \in Log.qs{1} = x \in LRO.m{1})).
proc. sp.   inline*. wp.  rnd. wp. skip.  smt.  skip. progress.  smt. smt.
seq 3 4 : (x{1} = G1'.x{2}  /\
  ((! (G1'.x{2} \in Log.qs{2}) =>
      (={glob D, glob LRO}
        /\ G0.y{1} = G1'.y{2}
        /\ G0.z{1} = G1'.z{2}
        /\ (G1'.mm.[G1'.x] = None){2}
        /\ eq_except (pred1 G1'.x{2}) G0.mm{1} G1'.mm{2}
        /\ LRO.m{1}.[G1'.x{2}] = Some G0.y{1}
        /\ (eq_except_l (pred1 G1'.x{2}) Log.qs{1} Log.qs{2})
        /\ 1 + size Log.qs{2} = size Log.qs{1})))).
seq 1 1 : (x{1} = G1'.x{2} /\ ((! (G1'.x{2} \in Log.qs{2})) =>
  (eq_except_l (pred1 G1'.x{2}) Log.qs{1} Log.qs{2})
    /\ ={glob D} /\ eq_except (pred1 G1'.x{2}) LRO.m{1} LRO.m{2}
    /\ G0.mm{1} = G1'.mm{2}
    /\ (G1'.mm.[G1'.x] = None){2}
    /\ (forall x, (x \in Log.qs{2}) = x \in LRO.m{2} )
    /\ (forall x, x \in Log.qs{1} = x \in LRO.m{1})
    /\ LRO.m{1}.[G1'.x{2}] = Some G0.y{1}
    /\ G0.y{1} = G1'.y{2}
    /\ G0.z{1} = G1'.z{2}
    /\ 1 + size Log.qs{2} = size Log.qs{1})).
inline*. wp. rnd. wp. skip. progress. smt. smt. smt. smt. smt. smt. smt. smt. smt. smt. smt. smt. smt.
smt. smt. smt. smt. 
seq 1 1 : (  x{1} = G1'.x{2} /\
  ((! (G1'.x{2} \in Log.qs{2})) =>
   (={glob D} /\
   (forall (x0 : in_t), (x0 \in Log.qs{2}) = (x0 \in LRO.m{2})) /\
   (forall (x0 : in_t), (x0 \in Log.qs{1}) = (x0 \in LRO.m{1})) /\
   (forall x, !(x \in Log.qs{2}) => LRO.m.[x]{2} = None) /\
   G0.y{1} = G1'.y{2} /\ G0.z{1} = G1'.z{2} /\ (G1'.mm.[G1'.x] = None){2} /\
   eq_except (pred1 G1'.x{2}) G0.mm{1} G1'.mm{2} /\
   LRO.m{1}.[G1'.x{2}] = Some G0.y{1} /\
   eq_except (pred1 G1'.x{2}) LRO.m{1} LRO.m{2}) /\
   eq_except_l (pred1 G1'.x{2}) Log.qs{1} Log.qs{2} /\
   1 + size Log.qs{2} = size Log.qs{1})).
call (_: G1'.x \in Log.qs,
      (forall x, x \in Log.qs{2} = x \in LRO.m{2})
      /\ (forall x, x \in Log.qs{1} = x \in LRO.m{1})
      /\ G0.y{1} = G1'.y{2} /\ G0.z{1} = G1'.z{2}
      /\ (G1'.mm.[G1'.x] = None){2}
      /\ eq_except (pred1 G1'.x{2}) G0.mm{1} G1'.mm{2}
      /\ eq_except (pred1 G1'.x{2}) LRO.m{1} LRO.m{2}
      /\ (eq_except_l (pred1 G1'.x{2}) Log.qs{1} Log.qs{2})
      /\  LRO.m{1}.[G1'.x{2}] = Some G0.y{1}
      /\ 1 + size Log.qs{2} = size Log.qs{1}).
apply D_a2_ll.
proc. sp.    inline*. wp.  rnd. wp.  skip. progress.  smt.  smt. smt. smt. smt. smt.  smt. smt.
smt. smt. smt. smt. smt. smt. smt. smt. smt.
apply eel1. auto. smt. smt. smt. smt. smt. smt. smt.
progress. proc. inline*. auto. smt.
progress. proc. sp. inline*. wp. rnd. wp.
skip. progress. smt. smt.
skip. progress. smt. smt.  smt. smt. smt. smt.  smt.   smt.   smt.  smt. smt.  smt.    smt. smt.  smt. smt. smt.   smt. smt. smt. smt. smt. smt. smt.
wp. skip. progress. smt.
  have : eq_except (pred1 G1'.x{2}) LRO.m{1} LRO.m{2}. smt.
move => R1.
have : G0.y{1} = G1'.y{2}. smt.
move => R2.
have : LRO.m{1}.[G1'.x{2}] = Some G0.y{1}. smt. smt (eq_except_set_getlr). smt.
smt.  smt.  smt.
smt. smt. smt.
sp.
call (_: (G1'.x \in G_bad.mqs),
      ={glob LRO}
      /\ eq_except (pred1 G1'.x{2}) G0.mm{1} G1'.mm{2}
      /\ eq_except_l (pred1 G1'.x{2}) Log.qs{1} Log.qs{2}
      /\ 1 + size Log.qs{2} = size Log.qs{1}).
apply D_a3_ll.
proc.  inline*. sp.  wp. rnd. wp. skip.
progress. apply eel1.  smt. smt.
apply eel1. smt. smt.  
progress. proc. inline*. auto. smt.
move =>_. proc. inline*. auto. progress.  smt. skip.
progress. smt. smt. smt. smt.  smt.  smt.
have : 1 + size qs_R = size qs_L. smt.
rewrite /P.
smt.
rewrite Pr [mu_or]. smt(mu_bounded).
qed.


end section.


require import FSet SmtMap.
require import AllCore List Distr Dexcepted FelTactic.
require import StdOrder StdBigop Finite.
import RealOrder Bigreal.

op supp_size (d : 'a distr) : int = size (to_seq (support d)).


module type HitAdversary (O:Oracle) = {
   proc play(x : in_t * out_t) : unit {O.o}
}.


module HitMain (O:Oracle) (A:HitAdversary) = {
  proc main(x : in_t * out_t) = {
     A(O).play(x);
  }
}.


axiom qH_pos :  1 <= qH.
axiom bdd : 1 <= supp_size dout.

axiom dout_ll1  : is_lossless dout.
axiom dout_ll2  : is_uniform dout.


lemma hitlemma' : forall (A <:HitAdversary {LRO, Log}) c l, 
 phoare[ HitMain(Log(LRO), A).main : arg.`2 = c /\ l = size Log.qs /\
     lookupc LRO.m c = false /\ ((card (fdom LRO.m)) <= 1 + size Log.qs) ==> lookupc LRO.m c = true
       /\ (size Log.qs) <= qH ] <= (qH%r / (supp_size dout)%r).
move => A c l. bypr. move => &m eq.
 fel 0 (size Log.qs - l) (fun x => 1%r / (supp_size dout)%r) 
     qH 
    (lookupc LRO.m c = true /\ (size Log.qs) <= qH)
    [Log(LRO).o : (size Log.qs <= qH)]
    ((card (fdom LRO.m)) <= 1 + size Log.qs). 
    rewrite BRA.sumr_const RField.intmulr count_predT.  
     smt (size_range qH_pos). smt. 
skip.  smt. 
proc.  inline*.  wp.  
conseq (_: _ ==> lookupc LRO.m.[x0 <- r0] c = true). smt.
rnd.  wp. skip. progress.
have ->: (fun (o : out_t) => lookupc (LRO.m{hr}.[x{hr} <- o]) c = true) 
   = (fun (o : out_t) => o = c). smt.
rewrite mu1_uni_ll. smt. smt. smt.
move => c0. proc. inline*. wp.  rnd. wp. 
skip. progress. smt.  clear H1 H2. clear H.  clear eq. smt. 
smt. smt. 
move => b c0. 
proc. inline*. sp.  wp.  rnd. wp. 
skip. progress. smt.    smt.  clear H1 H2. clear H. clear eq. smt.  smt.
smt.  smt.
qed.


lemma hitlemma : forall (A <:HitAdversary {LRO, Log}) c l, 
 phoare[ A(Log(LRO)).play : arg.`2 = c /\ l = size Log.qs /\
     lookupc LRO.m c = false /\ ((card (fdom LRO.m)) <= 1 + size Log.qs) ==> lookupc LRO.m c = true
       /\ (size Log.qs) <= qH  ] <= (qH%r / (supp_size dout)%r).
proof.  progress. bypr. progress.
have ->: Pr[A(Log(LRO)).play(x{m}) @ &m : lookupc LRO.m x{m}.`2 = true /\ size Log.qs <= qH]
  = Pr[ HitMain(Log(LRO), A).main(x{m}) @ &m : lookupc LRO.m x{m}.`2 = true /\ size Log.qs <= qH]. byequiv.
proc*.  inline*.  sp. call (_: ={glob Log, glob LRO}).  sim.
skip. auto. auto. auto.
byphoare (_:   arg = x{m} /\
     lookupc LRO.m arg.`2 = false /\ ((card (fdom LRO.m)) <= 1 + size Log.qs
 /\ size Log.qs = size Log.qs{m}) ==> _).
conseq (hitlemma' A x{m}.`2 (size Log.qs{m})). progress. smt. 
auto. auto.
qed.


module type DupAdversary (O:Oracle) = {
   proc play(x : dup_t) : unit {O.o}
}.

module DupMain (O:Oracle) (A:DupAdversary) = {
  proc main(x : dup_t) = {
    var r;
    O.init();
    r <@ A(O).play(x);
    return r;
  }
}.




require import SmtMap.

lemma winPr &m i : forall (A <:DupAdversary {LRO, Log}), 
 Pr[ DupMain(Log(LRO),A).main(i) @ &m : hasdup LRO.m /\ size Log.qs <= qH ] 
    <= qH%r * qH%r  / (supp_size dout)%r. 
proof. move => A. 
  fel 1 (size Log.qs) (fun x => qH%r / (supp_size dout)%r) qH (hasdup LRO.m) 
        [LRO.o : ( size Log.qs < qH)] ( (card (fdom LRO.m)) <= size Log.qs) => //.
   rewrite BRA.sumr_const RField.intmulr count_predT.
   smt (size_range qH_pos).
   inline *;auto.
   progress.  rewrite hde. auto. smt.
   proc. inline *.  
  case (x \notin LRO.m). sp.
  rcondt 2. rnd. skip. auto.
  wp.  rnd.  skip.  progress. 
  have ->: (fun (o : out_t) => hasdup LRO.m{hr}.[x{hr} <- o]) = mem (to_seq (rng LRO.m{hr})). 
apply fun_ext. move => o. rewrite thm11. auto. auto. auto.
apply (ler_trans ((BRA.big predT (fun x => mu1 dout x) (to_seq (rng LRO.m{hr}))))). 
apply mu_mem_le.
apply (ler_trans (BRA.big predT (fun (_ : out_t) => 1%r / (supp_size dout)%r)
   (to_seq (rng LRO.m{hr})))). 
apply ler_sum. progress. smt.
rewrite sumr_const. 
have ->: (count predT (to_seq (rng LRO.m{hr})))%r = (size (to_seq (rng LRO.m{hr})))%r. smt.
have ->:  size (to_seq (rng LRO.m{hr})) = card ((frng LRO.m{hr})). 
  have : uniq (to_seq (rng LRO.m{hr})). 
  apply uniq_to_seq. smt (@SmtMap).
  move => up. rewrite wtp. auto. smt.
smt.
  sp.  rcondf 2.  rnd. skip. auto.
  hoare. progress. smt. wp. rnd. skip. auto.
   move=> c. proc.  inline *. sp.
  wp. 
 rnd.  skip. timeout 20. smt.
qed.


end OnBound.
end ROM_BadCall.
