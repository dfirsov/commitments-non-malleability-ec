pragma Goals:printall.
require import DBool List Real Finite FSet.
require import Commitment.
require import Distr AllCore.
require import HelperFuns.


require NSNM_Definition.


require  LRO.

type message,  commitment,  openingkey, advice.

clone import NSNM_Definition as NSNM_def  with type value  <- unit,
                                           type message    <- message,
                                           type commitment <- commitment,
                                           type openingkey <- openingkey.


clone import CommitmentProtocol as CP with type value      <- unit,
                                           type message    <- message,
                                           type commitment <- commitment,
                                           type openingkey <- openingkey.


                                           
op rt_distr : openingkey distr.
op dout_distr: commitment distr.


axiom rt_distr_ll : is_lossless rt_distr.
axiom dout_distr_ll : is_lossless dout_distr.




clone import LRO as R with type out_t <- commitment,
                           type in_t  <- openingkey * message,
                           type dup_t <- advice,
                           type hit_t <- (openingkey * message) * commitment,
                           type d_in_t <- advice,
                           op   dout  <- dout_distr.                              

import R.RM.Lazy.





clone import R.ROM_BadCall as B.
clone import B.OnBound as OB.

(* This is the implementation of commitment scheme C^k_n from the paper *)
module RomCom (H : Oracle) : CommitmentScheme = {   
  proc gen() = {
    H.init();
  }
  
  proc commit(x : unit, m : message) : commitment * openingkey = {
    var d, c;
    d <$ rt_distr;
    c <- H.o(d,m);
    return (c, d);
  }

  proc verify(x : unit, m : message, c : commitment, d : openingkey) : bool = {
   var y;
   y <- H.o(d,m);
   return y = c;
  } 
}.


module type AdvROSNM (H : POracle) = {
  proc init(pk:unit, h : advice) : message distr * snm_relation {}
  proc commit(c : commitment, r : snm_relation) : commitment 
  proc decommit(d : openingkey) : openingkey  * message 
}.


module SNM_ROM_G0(CS:CommitmentScheme, A : AdvSNM) = {
  var c, c' : commitment
  var d, d' : openingkey
  var m, m' : message
  var v : bool
  proc main(h : advice) : bool = {
    var pk, ssnmdistr, rel;    
    pk                 <- CS.gen(); 
    (ssnmdistr, rel)   <- A.init(pk,h);
    m                  <$ ssnmdistr;
    (c, d)             <- CS.commit(pk, m);
    c'                 <- A.commit(c, rel);
    (d', m')           <- A.decommit(d);    
    v                  <- CS.verify(pk, m', c', d');
    return v /\ rel m m' /\ (c,d) <> (c',d');
  }
}.


module SNM_ROM_G1(CS:CommitmentScheme, A : AdvSNM, S : Simulator) = {
  var  m, m' : message
  proc main(h : advice) : bool = {
    var pk, ssnmdistr, rel;    
    pk                 <- CS.gen(); 
    (ssnmdistr, rel)   <- A.init(pk, h);
    m                  <$ ssnmdistr;
    m'                 <- S.simulate(pk, rel, ssnmdistr);
    return rel m m';
  }
}.



require import SmtMap.


section.

declare module BA : AdvROSNM {Log, LRO, G0, G_bad, SNM_ROM_G0, G1', SNM_ROM_G1}.


local module (G0HA : HitAdversary) (RO : Oracle)  = {
  module A = BA(RO)
  module CS = RomCom(RO)
    var d'  : openingkey
    var m' : message
    var b : bool
    proc play(dm : (openingkey * message), c' : commitment) = {
      (d', m') <- A.decommit(dm.`1);    
      b        <- CS.verify(tt, m', c', d');
  }
}.

local module G0H(RO : Oracle, CS : CommitmentScheme, A : AdvSNM) = {
  var c, c' : commitment
  var d : openingkey
  var m : message
  var v : bool
  var mm : (openingkey * message, commitment) fmap
  module G = G0HA(RO)
  proc main(h : advice)  = {
    var pk,ssnmdistr, rel;    
    mm                 <- empty;
    RO.init();
    pk                 <- CS.gen(); 
    (ssnmdistr, rel)   <- A.init(pk, h);
    m                  <$ ssnmdistr;
    d                  <$ rt_distr;
    c                  <$ dout_distr; 
    c'                 <- A.commit(c, rel);
    mm                 <- LRO.m;    
    LRO.m              <- LRO.m.[(d,m) <- c];
    G.play((d,G.m'),c');
  }
}.


axiom BA_ll0 : forall (H1 <: POracle{BA}), islossless H1.o 
   => phoare[ BA(H1).init : true ==> is_lossless res.`1 ] = 1%r.

axiom BA_ll1 : forall (H1 <: POracle{BA}), islossless H1.o => islossless BA(H1).commit.
axiom BA_ll2 : forall (H1 <: POracle{BA}), islossless H1.o => islossless BA(H1).decommit.
(* axiom snmdistr_ll: is_lossless snmdistr. *)


require import FSet.
axiom LogLRO : islossless Log(LRO).o.


local lemma Aqql &m rel: 
  Pr[G0H(Log(LRO), RomCom(Log(LRO)),BA(Log(LRO))).main(rel) @ &m :
    size Log.qs <= qH 
     /\ G0H.c <> G0H.c'
     /\ lookupc G0H.mm G0H.c' = false 
     /\ lookupc LRO.m G0H.c'  = true ] 
  <= (qH%r / (supp_size dout_distr)%r).
proof. byphoare =>//.
proc. 
seq 9 : (G0H.mm = LRO.m /\ ((card (fdom LRO.m))  <= size Log.qs)) (qH%r /(supp_size dout_distr)%r).
inline*. wp. call (_:true). conseq LogLRO.
rnd. rnd.  rnd.  
call (_: LRO.m = empty /\ G0H.mm = empty /\ Log.qs = []).
wp.  skip. auto.
wp =>//=.  call (_:true ==> true).
have ->: qH%r / ((supp_size dout_distr)%r * qH%r / (supp_size dout_distr)%r)
 = 1%r. smt.  bypr. smt.
rnd =>//. 
case (lookupc G0H.mm G0H.c' = false /\ G0H.c <> G0H.c').
conseq (_:(exists c'var, c'var = G0H.c') /\ exists lvar, lvar =  size Log.qs
/\ card (fdom LRO.m)  <= size Log.qs /\ G0H.mm = LRO.m /\ lookupc G0H.mm G0H.c' = false /\ G0H.c <> G0H.c' ==> _).
smt.
elim*. move => c'var lvar.
call (hitlemma G0HA c'var lvar). wp. skip. progress. smt(thm7). 
pose x := fdom LRO.m{hr}.
pose y := (fdom LRO.m{hr}.[G0H.d{hr}, G0H.m{hr} <- G0H.c{hr}]).
have : x \subset y. smt. move => h. apply subset_leq_fcard in h.
case(card x = card y). smt. progress. 
case((G0H.d{hr}, G0H.m{hr}) \in LRO.m{hr}). progress.
have : x = y. apply fsetP. smt. progress. smt. progress.
have : card x < card y. smt. rewrite /card. progress.  
have : x <> y. smt. progress.
case(x = fset0). smt. progress.
have : size(elems y) - size(elems x) = 1. smt. progress. smt. 
hoare.  smt.
conseq (_: _ ==> !(G0H.c <> G0H.c' /\
     lookupc G0H.mm G0H.c' = false)). smt.
inline*.  wp.  rnd.  wp. call (_: !(lookupc G0H.mm G0H.c' = false /\ G0H.c <> G0H.c')).
proc. inline*. wp. rnd. wp. skip. smt. wp. skip. progress. smt.
hoare. simplify. wp =>//=. 
call (_: card (fdom LRO.m) <= size Log.qs). 
proc. inline*. wp. rnd. wp. skip. progress.
clear H1 H0. smt. smt.
rnd. rnd. rnd. inline*. 
call (_: LRO.m = empty /\ G0H.mm = empty /\ Log.qs = []).  
wp. skip. progress. smt.
progress.
have-> : (qH%r * qH%r /
((supp_size dout_distr)%r * (qH%r * (supp_size dout_distr)%r) /
 (supp_size dout_distr)%r) ) = ((qH%r * qH%r /
(qH%r * (supp_size dout_distr)%r))). smt. smt.  
qed.



local module (Aq : DupAdversary) (O : Oracle)  = {
  module CS = RomCom(O)  
  module A = BA(O)
  proc play(h : advice) : unit = {
    var  m, c, d, c', d', m', v, ssnmdistr, rel;
    (ssnmdistr, rel)   <- A.init(tt, h);
    m                  <$ ssnmdistr;
    (c, d)             <- CS.commit(tt, m);
    c'                 <- A.commit(c, rel);
    (d', m')           <- A.decommit(d);    
    v                  <- CS.verify(tt, m', c', d');
  }  
}.



    
local lemma Agl &m rel: 
  Pr[SNM_ROM_G0( RomCom(Log(LRO)),BA(Log(LRO))).main(rel) @ &m: res /\ size Log.qs <= qH /\ SNM_ROM_G0.c = SNM_ROM_G0.c' ]
 <= Pr[SNM_ROM_G0( RomCom(Log(LRO)),BA(Log(LRO))).main(rel) @ &m: size Log.qs <= qH /\ hasdup LRO.m ].
proof. byequiv (_: ={glob LRO, glob BA, glob SNM_ROM_G0, h, glob Log} ==> _) =>//. proc.
conseq (_: _ ==> (SNM_ROM_G0.v{1} /\
     SNM_ROM_G0.d{1} <> SNM_ROM_G0.d'{1}) /\
  SNM_ROM_G0.c{1} = SNM_ROM_G0.c'{1} /\ size Log.qs{1} <= qH => size Log.qs{2} <= qH /\ hasdup LRO.m{2}). smt.
seq 4 4 : (={glob BA, rel, glob SNM_ROM_G0, glob LRO, glob Log} /\ (LRO.m.[(SNM_ROM_G0.d,SNM_ROM_G0.m)] = Some SNM_ROM_G0.c){1}).
inline*. wp. rnd. wp. rnd. wp.  rnd.
call (_:true). wp. skip. progress. smt. smt. 
seq 3 3 : (={glob BA, rel,  glob SNM_ROM_G0, glob LRO, glob Log} /\ (LRO.m.[(SNM_ROM_G0.d,SNM_ROM_G0.m)] = Some SNM_ROM_G0.c){1}
  /\ (SNM_ROM_G0.v => (LRO.m.[(SNM_ROM_G0.d',SNM_ROM_G0.m')] = Some SNM_ROM_G0.c')){1}).
inline*. 
wp.  rnd.  wp.  
call (_: (={glob SNM_ROM_G0, glob LRO, glob Log} /\ (LRO.m.[(SNM_ROM_G0.d,SNM_ROM_G0.m)] = Some SNM_ROM_G0.c){1})). 
proc. inline*.  wp.  rnd. wp. skip. progress. smt.
call (_: (={glob SNM_ROM_G0, glob LRO, glob Log} /\ (LRO.m.[(SNM_ROM_G0.d,SNM_ROM_G0.m)] = Some SNM_ROM_G0.c){1})). 
proc. inline*.  wp.  rnd. wp. skip. progress. smt.
skip. progress.
smt. smt. smt.
skip. progress. smt(thm6).
qed.


local lemma Aql &m rel: 
  Pr[SNM_ROM_G0( RomCom(Log(LRO)),BA(Log(LRO))).main(rel) @ &m: size Log.qs <= qH /\ hasdup LRO.m  ]
  <= (qH%r * qH%r) / (supp_size dout_distr)%r.
proof. 
have ->: Pr[SNM_ROM_G0(RomCom(Log(LRO)),BA(Log(LRO))).main(rel) @ &m: size Log.qs <= qH /\ hasdup LRO.m ]
  = Pr[DupMain(Log(LRO), Aq).main(rel) @ &m : size Log.qs <= qH /\ hasdup LRO.m].
byequiv =>//. proc. 
inline*. sim. 
call (_: ={glob Log, glob LRO}). wp. skip =>//. 
have ->: Pr[DupMain(Log(LRO), Aq).main(rel) @ &m : size Log.qs <= qH /\ hasdup LRO.m]
 = Pr[DupMain(Log(LRO), Aq).main(rel) @ &m : hasdup LRO.m /\ size Log.qs <= qH]. rewrite Pr[mu_eq]=>//. 
apply (winPr &m rel Aq).
qed.


local module (MD : Dist) (H : Oracle) = {
  module B = BA(H)
  module CS = RomCom(H)
  var d,d' : openingkey
  var m,m' : message
  var rel : snm_relation
  var cc, c' : commitment
  var ssnmdistr : message distr
  proc a1(h : advice) : openingkey * message = {
    var x;
    (ssnmdistr, x) <- B.init(tt,h);
    m    <$ ssnmdistr;
    d    <$ rt_distr;
    rel  <- x;
    return (d, m);
  }  
  proc a2(c : commitment) : commitment  = {
    cc    <- c;
    MD.c' <- B.commit(c, rel);
    return  c';
  }
  proc a3(c' : commitment) : bool = {
    var  v;
    (d', m') <- B.decommit(d);
    v <- CS.verify(tt, m', c', d');
    return v /\ rel m m' /\ (cc,d) <> (c',d') ;
  }
}.


local lemma g_bad_pr1 &m mrel:
 Pr[G_bad(MD,LRO).main(mrel) @ &m: res] <=
  Pr[G_bad(MD,LRO).main(mrel) @ &m: MD.d \in (map fst G_bad.mqs) ].
proof. byequiv =>//. proc. inline*. wp. rnd. wp. call (_: ={glob LRO, glob Log}). sim.
wp. call (_: ={glob LRO, glob Log}). sim. wp.  rnd.  wp. rnd. rnd.  call (_:true). wp. skip.
progress. rewrite pairS in H7. smt. 
qed.


axiom pr2_ax : phoare[ BA(Log(LRO)).commit : Log.qs = [] ==> size Log.qs <= qH ] = 1%r.

axiom bdd1 : 1 <= supp_size rt_distr.
axiom bdd2 :  is_uniform rt_distr.
axiom bdd3 :  is_lossless rt_distr.

require import Distr. 

require import FSet SmtMap.
require import AllCore List Distr Dexcepted FelTactic.
require import StdOrder StdBigop Finite.
import RealOrder Bigreal.


local lemma g_bad_pr2 &m mrel:
  Pr[G_bad(MD,LRO).main(mrel) @ &m: (MD.d) \in (map fst G_bad.mqs) ] <= (qH%r / (supp_size rt_distr)%r).
proof. byphoare =>//. proc. inline*.
swap 16 -1.
swap 9 6.
swap 7 7.
seq 13 : (size Log.qs <= qH /\ G_bad.mqs = Log.qs) (qH%r / (supp_size rt_distr)%r). auto.   
have q : qH%r / (supp_size rt_distr)%r / (qH%r / (supp_size rt_distr)%r) = 1%r.  smt.
wp. 
  have zz : phoare[ MD(Log(LRO)).B.commit : Log.qs = [] ==> size Log.qs <= qH] <= (
  qH%r / (supp_size rt_distr)%r / (qH%r / (supp_size rt_distr)%r)).
   rewrite q. conseq pr2_ax. 
call zz. wp.  rnd. wp. rnd. call (_:true). wp. skip =>//. 
seq 1 : (MD.d \in unzip1 G_bad.mqs) (qH%r / (supp_size rt_distr)%r) 1%r 1%r 0%r. 
auto. rnd. skip. progress. 
have ->: (mem (unzip1 Log.qs{hr})) = (mem (undup (unzip1 Log.qs{hr}))). smt.
rewrite mu_mem_uniq. smt. 
have iz : size (undup (unzip1 Log.qs{hr})) <= qH. smt.
have ok : (BRA.big predT (fun (x : openingkey) => mu1 rt_distr x)
   (undup (unzip1 Log.qs{hr}))) <= (BRA.big predT (fun (x : openingkey) => 1%r / (supp_size rt_distr)%r )
   (undup (unzip1 Log.qs{hr}))).
apply ler_sum_seq. smt.
apply (ler_trans (BRA.big predT (fun (x : openingkey) => 1%r / (supp_size rt_distr)%r )
   (undup (unzip1 Log.qs{hr})))). apply ok.
clear ok.
rewrite sumr_const. smt.
wp. rnd.  wp.  call (_:true ==> true). auto. wp. skip=>//. 
hoare. wp. rnd.  wp.  call (_:true ==> true). auto. wp.  skip=>//.
auto. hoare. simplify. auto. simplify. 
have qz : hoare[ BA(Log(LRO)).commit : Log.qs = [] ==> size Log.qs <= qH ].
conseq pr2_ax.
call qz. wp. rnd. wp. rnd. call (_:true). wp. skip =>//. progress.
have ->: (qH%r * qH%r /
 ((supp_size rt_distr)%r * (qH%r * (supp_size rt_distr)%r) / (supp_size rt_distr)%r)) =
(qH%r * qH%r /
((supp_size rt_distr)%r * qH%r)). smt. smt.  
qed.


local lemma zozzo &m rel : 
 Pr[G1'(MD,LRO).main(rel) @ &m: res /\ lookupc G1'.mm G1'.z = false ]
  <= Pr[G0H(Log(LRO), RomCom(Log(LRO)),BA(Log(LRO))).main(rel) @ &m :
         size Log.qs <= qH 
      /\ G0H.c <> G0H.c'
      /\ lookupc G0H.mm G0H.c' = false 
      /\ lookupc LRO.m G0H.c'  = true ].
proof. byequiv =>//. proc. inline*. wp. rnd. wp. call (_: ={glob LRO, glob Log}). sim.
wp. call (_: ={glob LRO, glob Log}). sim. wp. rnd. wp. rnd.  rnd. call (_:true). wp.
skip. progress. smt. smt. smt. smt.
qed.


local lemma qqq rel &m : 
 Pr[G0(MD,LRO).main(rel) @ &m: res] =
  Pr[SNM_ROM_G0(RomCom(Log(LRO)),BA(Log(LRO))).main(rel) @ &m: res /\ !hasdup LRO.m /\ size Log.qs <= qH /\ SNM_ROM_G0.c <> SNM_ROM_G0.c' ] .
proof. byequiv =>//. proc. inline*. wp. rnd. wp. call (_: ={glob LRO, glob Log}).
proc. inline*. wp. rnd. wp. skip. progress.
  wp. call (_: ={glob LRO, glob Log}). sim. wp. rnd. wp. rnd.
  wp. rnd. call (_:true). wp. skip. timeout 20. smt.
qed.


local lemma SNM_ROM_BadCall &m rel :
 Pr[SNM_ROM_G0(RomCom(Log(LRO)),BA(Log(LRO))).main(rel) @ &m: res /\ !hasdup LRO.m /\ size Log.qs <= qH /\ SNM_ROM_G0.c <> SNM_ROM_G0.c' ]
  <= Pr[G1'(MD,LRO).main(rel) @ &m: res]
   + Pr[G_bad(MD,LRO).main(rel) @ &m: res].
proof.
rewrite - qqq. apply (ROM_BadCall MD). 
progress. proc. wp. rnd. rnd. call (_:true ==> is_lossless res.`1).  
proc*. call (BA_ll0 H). skip =>//.
skip. progress. smt. auto.
progress. proc. inline*. call (_:true). apply BA_ll1. wp. skip=>//.
progress. proc. inline*. wp. call H0. wp. call (_:true). apply BA_ll2. skip=>//.
progress. apply dout_distr_ll. smt.
qed.



local lemma Cql'' &m rel : 
  Pr[G1'(MD,LRO).main(rel) @ &m:  G1'.mm.[G1'.x] = None /\ !sbset G1'.mm LRO.m ] = 0%r.
proof. byphoare =>//. hoare. proc.
seq 7 : (G1'.mm = LRO.m). auto. simplify.  auto. 
case (G1'.mm.[G1'.x] = None).
sp 1. elim*. progress.
conseq (_: sbset G1'.mm LRO.m /\  G1'.mm.[G1'.x] = None  ==> _). smt.
inline*. wp. rnd. wp.  
call (_: (sbset G1'.mm LRO.m) ). 
proc. inline*. wp. rnd. wp. skip. smt. 
wp. skip. smt.
inline*.  wp. rnd. wp. call (_:true). auto. 
wp. skip. progress. smt. smt. 
qed.


local lemma Cql' &m rel : 
  Pr[G1'(MD,LRO).main(rel) @ &m:  res /\ lookupc G1'.mm G1'.z = true /\ !sbset G1'.mm LRO.m ] 
 <=   0%r .
proof. rewrite - (Cql'' &m rel). byequiv =>//. proc. inline*. wp. rnd. wp.
call (_: ={glob LRO, glob Log, G1'.mm, G1'.x, G1'.z,G1'.y}). sim.
wp. call (_: ={glob LRO, glob Log, G1'.mm, G1'.x, G1'.z,G1'.y}). sim.
wp. rnd. wp. rnd. rnd. call (_:true). wp. skip. progress. 
qed.


local lemma Cql &m rel : 
  Pr[G1'(MD,LRO).main(rel) @ &m: res  /\ lookupc G1'.mm G1'.z = true ]
 = Pr[G1'(MD,LRO).main(rel) @ &m: res /\ lookupc G1'.mm G1'.z = true
      /\ sbset G1'.mm LRO.m ].
proof. rewrite Pr[mu_split (sbset G1'.mm LRO.m)].
have ->: Pr[G1'(MD, LRO).main(rel) @ &m :  (res /\ lookupc G1'.mm G1'.z = true) /\ ! sbset G1'.mm LRO.m]
 = Pr[G1'(MD, LRO).main(rel) @ &m : res /\ lookupc G1'.mm G1'.z = true /\ !sbset G1'.mm LRO.m].
rewrite Pr[mu_eq] =>//. 
have ->: Pr[G1'(MD, LRO).main(rel) @ &m :  (res /\ lookupc G1'.mm G1'.z = true) /\ sbset G1'.mm LRO.m]
 = Pr[G1'(MD, LRO).main(rel) @ &m : res /\ lookupc G1'.mm G1'.z = true /\ sbset G1'.mm LRO.m].
rewrite Pr[mu_eq] =>//. 
have ->: Pr[G1'(MD, LRO).main(rel) @ &m : res /\ lookupc G1'.mm G1'.z = true /\ !sbset G1'.mm LRO.m] = 0%r.
smt. auto.
qed.


local lemma Dql &m rel :
 Pr[G1'(MD,LRO).main(rel) @ &m: res      /\ lookupc G1'.mm G1'.z = true
  /\ sbset G1'.mm LRO.m ]
 = Pr[G1'(MD,LRO).main(rel) @ &m: res      /\ lookupc G1'.mm G1'.z = true
  /\ sbset G1'.mm LRO.m  /\ (head witness (solve G1'.mm G1'.z)) = (MD.d',MD.m')  ].
proof.
byequiv (_: (={glob G1', glob Log, glob LRO, glob MD, arg}) ==> _) =>//.
proc.
seq 9 9 : (={glob G1', glob Log, glob LRO, glob MD} /\ (G1'.mm.[G1'.x] = None => sbset G1'.mm LRO.m){1} ). 
seq 6 6 : (={glob G1', glob Log, glob LRO, glob MD}). inline*.
wp. call (_: ={glob LRO, glob Log, glob G1', MD.c', MD.d,MD.d',MD.rel,MD.cc}). sim.
wp. rnd. wp. rnd. rnd. call (_: ={glob LRO, glob Log, glob G1', MD.c', MD.d,MD.d',MD.rel,MD.cc}). wp. skip. progress.
wp. skip. progress. smt.
case (G1'.mm{1}.[G1'.x{1}] = None).
conseq (_: (={glob G1', glob Log, glob LRO, glob MD} /\ (sbset G1'.mm LRO.m){1} /\ G1'.mm.[G1'.x]{1} = None  ) ==> _). smt.
inline*. wp. rnd. wp. call (_: ={glob LRO, glob Log, MD.c', MD.d,MD.d',MD.rel,MD.cc,  G1'.mm} /\ (sbset G1'.mm LRO.m){1} /\ (G1'.mm.[G1'.x]{1} = None) ).
proc. inline*. wp. rnd. wp. skip. progress. smt.
wp. skip. progress.
have ->: (solve G1'.mm{2}
     (oget
        m_R.[result_R.`1, result_R.`2 <- r1L].[result_R.`1, result_R.`2]))
 = [(result_R.`1, result_R.`2)].
rewrite (thm1 (result_R.`1, result_R.`2) G1'.mm{2}). smt.
  have ->: m_R.[result_R.`1, result_R.`2 <- r1L].[result_R.`1, result_R.`2]
   = Some r1L. smt. simplify.
have : exists x, G1'.mm{2}.[x] = Some r1L. apply thm2. smt.
elim. move => x ass.
have f0 : m_R.[result_R.`1, result_R.`2 <- r1L].[x] = Some r1L.
clear H13 H12 H11 H10 H9 H8. smt.
have f1 : x = (result_R.`1, result_R.`2).
apply (thm3 (m_R.[result_R.`1, result_R.`2 <- r1L]) r1L ). simplify. smt. apply f0.
smt. rewrite - f1. apply ass. 
have : exists y, m_R.[result_R.`1, result_R.`2] = Some y. apply thm5.
rewrite /P' in H10. 
have : exists x, G1'.mm{2}.[x] = Some r1L. apply thm2. smt.
elim. move => x ass.
have f0 : m_R.[result_R.`1, result_R.`2 <- r1L].[x] = Some r1L.
clear H13 H12 H11 H10 H9 H8. smt. smt. 
elim. move => y yeq.
have : lookupc G1'.mm{2} y = true.
  have ->: y = (oget m_R.[result_R.`1, result_R.`2]). rewrite yeq =>//.
rewrite yeq. smt. 
   move => ff. smt. auto. smt.
have : exists y, m_R.[result_R.`1, result_R.`2] = Some y. apply thm5 =>//. 
elim. move => y yeq.
have : exists z, G1'.mm{2}.[z] = Some y.
apply (thm2 G1'.mm{2}). smt.
elim. move => z q.
have : m_R.[z] = Some y. 
clear H13 H12 H11 H10 H9 H8. smt.
move => qq.
have : z = (result_R.`1, result_R.`2). smt.
move => fff. rewrite - fff. smt.
conseq (_: G1'.mm{1}.[G1'.x{1}] <> None /\ G1'.mm{2}.[G1'.x{2}] <> None ==> (G1'.mm{1}.[G1'.x{1}] = None){1} <=> G1'.mm{2}.[G1'.x{2}] = None{2} ). smt. smt.
inline*. wp. rnd. wp. call (_: true ==> true).
proc*. call {1} (_:true ==> true). apply (BA_ll2 (Log(LRO)) ). proc. inline*. auto. smt.
call {2} (_:true ==> true). apply (BA_ll2 (Log(LRO)) ). proc. inline*. auto. smt. auto.
wp. skip. progress. 
qed.
  

require import StdRing StdOrder StdBigop.
(*---*) import RField  RealOrder.

lemma zzz (c a b : real) : a - c <= b - c => a <= b. smt.
qed.


local module MySim = {
  module B = BA(Log(LRO))
  var m' : message
  var c,c' : commitment
  var d,d' : openingkey
  proc simulate(pk : unit, rel : snm_relation, dd : message distr) = {
    G1'.mm <- empty;
    d    <$ rt_distr;
    c    <$ dout_distr;
    c'   <- B.commit(c, rel);
    G1'.mm <- LRO.m;
    (d', m') <- (head witness (solve G1'.mm c'));
    return m';
  }
}.


local lemma zhok  &m mrel : 
 Pr[G1'(MD,LRO).main(mrel) @ &m:  res /\ lookupc G1'.mm G1'.z = true
           /\ sbset G1'.mm LRO.m /\ (head witness (solve G1'.mm G1'.z)) = (MD.d',MD.m') ]
 <= Pr[SNM_ROM_G1(RomCom(Log(LRO)), BA(LRO), MySim ).main(mrel) @ &m: res  ].
proof. byequiv =>//. proc. inline MD(Log(LRO)).a3.
seq 11 5 : (MD.m{1} = SNM_ROM_G1.m{2} /\ (((head witness (solve G1'.mm G1'.z)) = (MD.d',MD.m')){1} => MD.m'{1} = SNM_ROM_G1.m'{2}) /\ MD.rel{1} = rel{2}) .
inline*. wp. call {1} (_: true ==> true). 
apply (BA_ll2 (Log(LRO)) ). proc. inline*. auto. smt.
wp. call (_: ={glob LRO}). sim. wp. rnd. wp. rnd.  wp. rnd.  call (_:true). wp. skip.
progress. smt.
case ((head witness (solve G1'.mm{1} G1'.z{1}) = (MD.d'{1}, MD.m'{1}))).
conseq (_:  (MD.m{1} = SNM_ROM_G1.m{2} /\  
    MD.m'{1} = SNM_ROM_G1.m'{2}) /\
   MD.rel{1}  = rel{2} /\ (head witness (solve G1'.mm{1} G1'.z{1}) = (MD.d'{1}, MD.m'{1}))  ==> _).
smt.
inline*. wp. rnd {1}. wp. skip. progress. smt.
inline*. wp. rnd {1}. wp. skip. smt. 
qed.


local lemma snm_rom_f &m rel: 
   Pr[SNM_ROM_G0(RomCom(Log(LRO)),BA(Log(LRO))).main(rel) @ &m: res /\ size Log.qs <= qH]
   <= (qH%r * qH%r) / (supp_size dout_distr)%r
    + (qH%r * qH%r) / (supp_size dout_distr)%r
    + (qH%r / (supp_size dout_distr)%r)
    + Pr[G1'(MD,LRO).main(rel) @ &m: res /\ lookupc G1'.mm G1'.z = true
           /\ sbset G1'.mm LRO.m /\ (head witness (solve G1'.mm G1'.z)) = (MD.d',MD.m') ]
    + Pr[G_bad(MD,LRO).main(rel) @ &m: res].
proof. 
have ->: Pr[SNM_ROM_G0(RomCom(Log(LRO)),BA(Log(LRO))).main(rel) @ &m: res /\ size Log.qs <= qH]
 = Pr[SNM_ROM_G0(RomCom(Log(LRO)),BA(Log(LRO))).main(rel) @ &m: res /\ size Log.qs <= qH /\ SNM_ROM_G0.c = SNM_ROM_G0.c'  ]
 + Pr[SNM_ROM_G0(RomCom(Log(LRO)),BA(Log(LRO))).main(rel) @ &m: res /\ size Log.qs <= qH /\ SNM_ROM_G0.c <> SNM_ROM_G0.c'  ].
rewrite Pr[mu_split SNM_ROM_G0.c = SNM_ROM_G0.c']. 
 have ->: Pr[SNM_ROM_G0(RomCom(Log(LRO)), BA(Log(LRO))).main(rel) @ &m :
   (res /\ size Log.qs <= qH) /\ SNM_ROM_G0.c <> SNM_ROM_G0.c'] = Pr[SNM_ROM_G0(RomCom(Log(LRO)), BA(Log(LRO))).main(rel) @ &m :
   res /\ size Log.qs <= qH /\ SNM_ROM_G0.c <> SNM_ROM_G0.c']. rewrite Pr[mu_eq] =>//.
 have ->: Pr[SNM_ROM_G0(RomCom(Log(LRO)), BA(Log(LRO))).main(rel) @ &m :
   (res /\ size Log.qs <= qH) /\ SNM_ROM_G0.c = SNM_ROM_G0.c'] = Pr[SNM_ROM_G0(RomCom(Log(LRO)), BA(Log(LRO))).main(rel) @ &m :
   res /\ size Log.qs <= qH /\ SNM_ROM_G0.c = SNM_ROM_G0.c']. rewrite Pr[mu_eq] =>//. auto.
  have : Pr[SNM_ROM_G0(RomCom(Log(LRO)), BA(Log(LRO))).main(rel) @ &m :
   res /\ size Log.qs <= qH /\ SNM_ROM_G0.c = SNM_ROM_G0.c'] <= (qH%r * qH%r) / (supp_size dout_distr)%r.
   apply (ler_trans Pr[SNM_ROM_G0(RomCom(Log(LRO)), BA(Log(LRO))).main(rel) @ &m :
             size Log.qs <= qH  /\ hasdup LRO.m]). apply Agl.
      apply Aql.
move => f.
apply (ler_trans  (qH%r * qH%r / (supp_size dout_distr)%r +
Pr[SNM_ROM_G0(RomCom(Log(LRO)), BA(Log(LRO))).main(rel) @ &m :
   res /\ size Log.qs <= qH /\ SNM_ROM_G0.c <> SNM_ROM_G0.c']) ). smt. clear f.
apply (zzz (qH%r * qH%r / (supp_size dout_distr)%r)). 
have ->: qH%r * qH%r / (supp_size dout_distr)%r +
Pr[SNM_ROM_G0(RomCom(Log(LRO)), BA(Log(LRO))).main(rel) @ &m :
   res /\ size Log.qs <= qH /\ SNM_ROM_G0.c <> SNM_ROM_G0.c'] -
qH%r * qH%r / (supp_size dout_distr)%r 
 =  Pr[SNM_ROM_G0(RomCom(Log(LRO)), BA(Log(LRO))).main(rel) @ &m :
   res /\ size Log.qs <= qH /\ SNM_ROM_G0.c <> SNM_ROM_G0.c'].
smt.
have ->: qH%r * qH%r / (supp_size dout_distr)%r + qH%r * qH%r / (supp_size dout_distr)%r + qH%r / (supp_size dout_distr)%r +
Pr[G1'(MD, LRO).main(rel) @ &m :
   res /\
   lookupc G1'.mm G1'.z = true /\
   sbset G1'.mm LRO.m /\ head witness (solve G1'.mm G1'.z) = (MD.d', MD.m')] +
Pr[G_bad(MD, LRO).main(rel) @ &m : res] -
qH%r * qH%r / (supp_size dout_distr)%r = qH%r * qH%r / (supp_size dout_distr)%r +
qH%r / (supp_size dout_distr)%r +
Pr[G1'(MD, LRO).main(rel) @ &m :
   res /\
   lookupc G1'.mm G1'.z = true /\
   sbset G1'.mm LRO.m /\ head witness (solve G1'.mm G1'.z) = (MD.d', MD.m')] +
Pr[G_bad(MD, LRO).main(rel) @ &m : res].
smt.
have ->: Pr[SNM_ROM_G0(RomCom(Log(LRO)),BA(Log(LRO))).main(rel) @ &m: res /\ size Log.qs <= qH /\ SNM_ROM_G0.c <> SNM_ROM_G0.c'] = Pr[SNM_ROM_G0( RomCom(Log(LRO)),BA(Log(LRO))).main(rel) @ &m: res /\ size Log.qs <= qH /\ SNM_ROM_G0.c <> SNM_ROM_G0.c' /\ hasdup LRO.m]
 + Pr[SNM_ROM_G0( RomCom(Log(LRO)),BA(Log(LRO))).main(rel) @ &m: res /\ size Log.qs <= qH /\ SNM_ROM_G0.c <> SNM_ROM_G0.c' /\ !hasdup LRO.m]. 
rewrite Pr[mu_split (hasdup LRO.m)].
have ->: Pr[SNM_ROM_G0( RomCom(Log(LRO)), BA(Log(LRO))).main(rel) @ &m :
   (res /\ size Log.qs <= qH /\ SNM_ROM_G0.c <> SNM_ROM_G0.c') /\
   hasdup LRO.m] = Pr[SNM_ROM_G0(RomCom(Log(LRO)), BA(Log(LRO))).main(rel) @ &m :
   res /\ size Log.qs <= qH /\ SNM_ROM_G0.c <> SNM_ROM_G0.c' /\
   hasdup LRO.m]. rewrite Pr[mu_eq] =>//. 
have ->: Pr[SNM_ROM_G0( RomCom(Log(LRO)), BA(Log(LRO))).main(rel) @ &m :
   (res /\ size Log.qs <= qH /\ SNM_ROM_G0.c <> SNM_ROM_G0.c') /\
   !hasdup LRO.m] = Pr[SNM_ROM_G0(RomCom(Log(LRO)), BA(Log(LRO))).main(rel) @ &m :
   res /\ size Log.qs <= qH /\ SNM_ROM_G0.c <> SNM_ROM_G0.c' /\
   !hasdup LRO.m]. rewrite Pr[mu_eq] =>//. auto.
have : Pr[SNM_ROM_G0(RomCom(Log(LRO)), BA(Log(LRO))).main(rel) @ &m :
   res /\ size Log.qs <= qH /\ SNM_ROM_G0.c <> SNM_ROM_G0.c' /\ hasdup LRO.m]
 <= qH%r * qH%r / (supp_size dout_distr)%r .
apply (ler_trans Pr[SNM_ROM_G0(RomCom(Log(LRO)), BA(Log(LRO))).main(rel) @ &m :
             size Log.qs <= qH  /\ hasdup LRO.m]). rewrite Pr[mu_sub] =>//.
apply Aql. move => f.
apply (ler_trans (qH%r * qH%r / (supp_size dout_distr)%r +
Pr[SNM_ROM_G0(RomCom(Log(LRO)), BA(Log(LRO))).main(rel) @ &m :
   res /\
   size Log.qs <= qH /\ SNM_ROM_G0.c <> SNM_ROM_G0.c' /\ ! hasdup LRO.m])).
smt. clear f.
apply (zzz (qH%r * qH%r / (supp_size dout_distr)%r)). 
have ->: qH%r * qH%r / (supp_size dout_distr)%r +
Pr[SNM_ROM_G0(RomCom(Log(LRO)), BA(Log(LRO))).main(rel) @ &m :
   res /\
   size Log.qs <= qH /\ SNM_ROM_G0.c <> SNM_ROM_G0.c' /\ ! hasdup LRO.m] -
qH%r * qH%r / (supp_size dout_distr)%r = Pr[SNM_ROM_G0( RomCom(Log(LRO)), BA(Log(LRO))).main(rel) @ &m :
   res /\
   size Log.qs <= qH /\ SNM_ROM_G0.c <> SNM_ROM_G0.c' /\ ! hasdup LRO.m]. smt.
have ->: qH%r * qH%r / (supp_size dout_distr)%r + qH%r / (supp_size dout_distr)%r +
Pr[G1'(MD, LRO).main(rel) @ &m :
   res /\
   lookupc G1'.mm G1'.z = true /\
   sbset G1'.mm LRO.m /\ head witness (solve G1'.mm G1'.z) = (MD.d', MD.m')] +
Pr[G_bad(MD, LRO).main(rel) @ &m : res] -
qH%r * qH%r / (supp_size dout_distr)%r = qH%r / (supp_size dout_distr)%r +
Pr[G1'(MD, LRO).main(rel) @ &m :
   res /\
   lookupc G1'.mm G1'.z = true /\
   sbset G1'.mm LRO.m /\ head witness (solve G1'.mm G1'.z) = (MD.d', MD.m')] +
Pr[G_bad(MD, LRO).main(rel) @ &m : res] . smt.
apply (ler_trans (Pr[G1'(MD,LRO).main(rel) @ &m: res]
   + Pr[G_bad(MD,LRO).main(rel) @ &m: res])).
have ->: Pr[SNM_ROM_G0(RomCom(Log(LRO)), BA(Log(LRO))).main(rel) @ &m :
   res /\
   size Log.qs <= qH /\ SNM_ROM_G0.c <> SNM_ROM_G0.c' /\ ! hasdup LRO.m] =   Pr[SNM_ROM_G0( RomCom(Log(LRO)),BA(Log(LRO))).main(rel) @ &m: res /\ !hasdup LRO.m /\ size Log.qs <= qH /\ SNM_ROM_G0.c <> SNM_ROM_G0.c' ].
rewrite Pr[mu_eq] =>//.
apply SNM_ROM_BadCall.
apply (zzz Pr[G_bad(MD, LRO).main(rel) @ &m : res]).
have ->: Pr[G1'(MD, LRO).main(rel) @ &m : res] +
Pr[G_bad(MD, LRO).main(rel) @ &m : res] -
Pr[G_bad(MD, LRO).main(rel) @ &m : res] = Pr[G1'(MD, LRO).main(rel) @ &m : res]. smt.
have ->: qH%r / (supp_size dout_distr)%r +
Pr[G1'(MD, LRO).main(rel) @ &m :
   res /\
   lookupc G1'.mm G1'.z = true /\
   sbset G1'.mm LRO.m /\ head witness (solve G1'.mm G1'.z) = (MD.d', MD.m')] +
Pr[G_bad(MD, LRO).main(rel) @ &m : res] -
Pr[G_bad(MD, LRO).main(rel) @ &m : res] =  qH%r / (supp_size dout_distr)%r + Pr[G1'(MD, LRO).main(rel) @ &m :
   res /\
   lookupc G1'.mm G1'.z = true /\
   sbset G1'.mm LRO.m /\ head witness (solve G1'.mm G1'.z) = (MD.d', MD.m')].
smt.
rewrite Pr[mu_split (lookupc G1'.mm G1'.z = false)].
have : Pr[G1'(MD, LRO).main(rel) @ &m : res /\ lookupc G1'.mm G1'.z = false]
 <= qH%r / (supp_size dout_distr)%r.
apply (ler_trans Pr[G0H(Log(LRO), RomCom(Log(LRO)),BA(Log(LRO))).main(rel) @ &m :
         size Log.qs <= qH 
      /\ G0H.c <> G0H.c'
      /\ lookupc G0H.mm G0H.c' = false 
      /\ lookupc LRO.m G0H.c'  = true ]). apply zozzo.
apply Aqql.
move => f.
apply (ler_trans (qH%r / (supp_size dout_distr)%r +
Pr[G1'(MD, LRO).main(rel) @ &m : res /\ lookupc G1'.mm G1'.z <> false])). smt.
apply (zzz (qH%r / (supp_size dout_distr)%r)).
have ->: (qH%r / (supp_size dout_distr)%r) + Pr[G1'(MD, LRO).main(rel) @ &m : res /\ lookupc G1'.mm G1'.z <> false] - (qH%r / (supp_size dout_distr)%r) = Pr[G1'(MD, LRO).main(rel) @ &m : res /\ lookupc G1'.mm G1'.z <> false].
smt.
have ->: qH%r / (supp_size dout_distr)%r +
Pr[G1'(MD, LRO).main(rel) @ &m :   res /\   lookupc G1'.mm G1'.z = true /\   sbset G1'.mm LRO.m /\ head witness (solve G1'.mm G1'.z) = (MD.d', MD.m')] -
qH%r / (supp_size dout_distr)%r = Pr[G1'(MD, LRO).main(rel) @ &m :   res /\   lookupc G1'.mm G1'.z = true /\   sbset G1'.mm LRO.m /\ head witness (solve G1'.mm G1'.z) = (MD.d', MD.m')]. smt.
have ->: Pr[G1'(MD, LRO).main(rel) @ &m : res /\ lookupc G1'.mm G1'.z <> false] 
 = Pr[G1'(MD, LRO).main(rel) @ &m : res /\ lookupc G1'.mm G1'.z = true]. rewrite Pr[mu_eq] =>//. smt. 
rewrite Cql. rewrite Dql =>//.
qed.


local lemma nsnm_lro_sec &m h: 
   Pr[SEG0(RomCom(Log(LRO)),BA(Log(LRO))).main(h) @ &m: res /\ size Log.qs <= qH]
 - Pr[SEG1(RomCom(Log(LRO)), BA(LRO), MySim).main(h) @ &m: res  ]
 <=   (qH%r * qH%r) / (supp_size dout_distr)%r 
    + (qH%r * qH%r) / (supp_size dout_distr)%r
    + (qH%r / (supp_size dout_distr)%r)
    + (qH%r / (supp_size rt_distr)%r).
proof.
have ->: Pr[SEG0(RomCom(Log(LRO)),BA(Log(LRO))).main(h) @ &m: res /\ size Log.qs <= qH]
 = Pr[SNM_ROM_G0(RomCom(Log(LRO)),BA(Log(LRO))).main(h) @ &m: res /\ size Log.qs <= qH].
byequiv =>//. sim. 
have ->: Pr[SEG1(RomCom(Log(LRO)), BA(LRO), MySim).main(h) @ &m: res  ]
 =  Pr[SNM_ROM_G1(RomCom(Log(LRO)), BA(LRO), MySim).main(h) @ &m: res  ].
byequiv =>//. sim. smt (snm_rom_f zhok g_bad_pr1 g_bad_pr2).
qed.

