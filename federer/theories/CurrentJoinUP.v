(** Federer (1969), 4.1.11, p. 364: independent specification
    of the original join by the pushforward action of
    S times [0,1] times T under F(x,t,y)=(1-t)x+ty.
    All actual compact pullback replacements are retained.
    Existence, uniqueness and compactness are proved separately. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import RealNormUP NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  CurrentPushforwardUP CurrentJoinMapSealed CurrentJoinMapClass
  CurrentJoinDomain CurrentJoinSourceChain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section CurrentJoinUP.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n i j : nat.
Local Notation X := (R_n R n).
Local Notation Full := (fun _ : X => True).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hFull := (fun (x : X) (_ : True) =>
  @norm_full_domain_interior R X NX x).
Local Notation Domain := (@current_join_domain R n).
Local Notation hDomain := (@current_join_domain_open R n).
Variable S : @current_space R h2 n Full hFull i.
Variable T : @current_space R h2 n Full hFull j.
Local Notation Chain := (@current_join_source_chain R h2 n i j S T).
Local Notation F := (@CurrentJoinMap.value R n).
Local Notation Image := (@current_join_map_image R n).
Local Notation Smooth :=
  (@current_join_map_smooth R n Domain hDomain).

(** Source for [is_current_join]: the displayed defining
    equation for S join T, Federer 4.1.11, p. 364. The
    degree is the original i+1+j. The predicate imposes neither
    existence nor a mass, representation or compactness hypothesis. *)
Definition is_current_join
    (J : @current_space R h2 n Full hFull (i+1+j)%N) : Prop :=
  @is_current_pushforward R h2 (n+(1+n))%N n (i+1+j)%N
    Domain Full hDomain hFull Chain F Image Smooth J.
End CurrentJoinUP.
