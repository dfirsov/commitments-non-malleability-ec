pragma Goals:printall.
require import DBool List Real.
require import Commitment.
require import Distr AllCore.


require import D1D2.
require import NSNM_Definition.
require import NSNM_Pure_Binding.

require CommitmentUnpredictability.

clone import CommitmentProtocol as CP with type value      <- value,
                                           type message    <- message,
                                           type commitment <- commitment,
                                           type openingkey <- openingkey.

clone import NSNM_binding_theory as BE. 
import BE.CU.                  

op diff : value -> message -> message.
axiom diff_correct (pk : value) (m : message) : m <> diff pk m.


module A'(A : Binder) = {
  proc bind(x : value) = {    
    var pk, c, m, d, m', d', m3;
    pk <- x;
    (c, m, d, m', d') <@ A.bind(pk);
    m3 <- if (m=m') then diff pk m else m';
    return (c, m, d, m3, d'); 
  }
}.

section.

declare module A : Binder {A', B, G0}.
axiom Ag_ll : islossless A'(A).bind.

local lemma l1 &m :
  Pr[ BindingExperiment(A).main() @ &m : res ] <= Pr[ BindingExperiment(A'(A)).main() @ &m : res ].
proof.
byequiv =>//. proc. inline*.
wp. call(_:true). wp. rnd.
skip. progress.
rewrite H3. progress. 
rewrite H3. progress.     
qed. 


local lemma ba' : hoare [ A'(A).bind : true ==> res.`2 <> res.`4 ]. 
proof. 
proc. inline*.  
wp. call(_:true). wp. 
skip. progress.
smt. 
qed.


local lemma final &m h :  forall (S <: Simulator {A', B, A}),
  Pr[ BindingExperiment(A'(A)).main() @ &m : res ] <= 
  2%r * (Pr[ SG0(B(A'(A))).main(h) @ &m : res ] - Pr[ SG1(B(A'(A)),S).main(h) @ &m : res ]) 
   + 6%r * Pr[ UnpredGame(BG(A'(A))).main() @ &m : res ].
proof.
move => S.  
apply (nsnm_pure_binding (A'(A)) Ag_ll ba' &m h S ). 
qed. 


lemma nsnm_pure_binding_2 &m h :  forall (S <: Simulator {A', B, A}),
  Pr[ BindingExperiment(A).main() @ &m : res ] <= 
  2%r * (Pr[ SG0(B(A'(A))).main(h) @ &m : res ] - Pr[ SG1(B(A'(A)),S).main(h) @ &m : res ]) 
   + 6%r * Pr[ UnpredGame(BG(A'(A))).main() @ &m : res ].
proof.
move => S. 
have : Pr[ BindingExperiment(A).main() @ &m : res ] <= Pr[ BindingExperiment(A'(A)).main() @ &m : res ]. apply l1. progress.  
have : Pr[ BindingExperiment(A'(A)).main() @ &m : res ] <= 
  2%r * (Pr[ SG0(B(A'(A))).main(h) @ &m : res ] - Pr[ SG1(B(A'(A)),S).main(h) @ &m : res ]) 
   + 6%r * Pr[ UnpredGame(BG(A'(A))).main() @ &m : res ].
apply (nsnm_pure_binding_2 &m h S). progress.
smt. 
qed.

end section.
 












    



