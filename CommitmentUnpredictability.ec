
require import AllCore List. 

type value, commitment, openingkey, message.

op rndstr : (bool list) distr.

op Com (x : value) (r : bool list) (m : message) : commitment * openingkey.
op Ver : value -> message * (commitment * openingkey) -> bool.
op Dpk : value distr.


module type Guesser = {
  proc guess(pk : value) : message * (commitment * openingkey) list
}.


(* Guesser-adversary tries to compute a list "l" which would contain a
canonically generated commitment-opening pair. *)
module UnpredGame(G : Guesser) = {
  proc main() = {
    var pk,m,l,c,d,rs;
    pk      <$ Dpk;
    (m , l) <- G.guess(pk); 
    rs      <$ rndstr;
    (c, d)  <- Com pk rs m;
    return (c,d) \in l;
  }
}.
