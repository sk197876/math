(** Federer (1969), 3.1.21, p. 234: product tangent and
    normal planes have the asserted sum dimensions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear ModuleQuotient SubspaceSums SubspaceCarrier LinearBasis
  GrassmannSubspaces GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  ProductFiniteBasis EuclideanBlockLinearMaps LinearRankUP LinearInjectiveRank.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [grassmann_block_product_exists]: supporting the
    dimensions 2mu and n in the tangent and normal bundle
    assertions of Federer 3.1.21, p. 234. Products of
    a mu-plane and a nu-plane give a (mu+nu)-plane under
    the existing Euclidean block identification, including zero factors. *)
Theorem grassmann_block_product_exists (R:realType) n mu nu
    (Z:G (R_n R n) mu) (W:G (R_n R n) nu) :
  exists H:G (R_n R (n+n)) (mu+nu),forall x,
    grassmann_val H x <-> grassmann_val Z (@euclidean_first_block_map R n n x) /\
      grassmann_val W (@euclidean_last_block_map R n n x).
Proof.
pose X:=R_n R n.
pose P:=R_n R (n+n).
pose ZX:=subspace_space (grassmann_val Z).
pose WX:=subspace_space (grassmann_val W).
pose V:=GRing.Lmodule.clone R (ZX*WX)%type _.
pose p:=@euclidean_first_block_map R n n.
pose q:=@euclidean_last_block_map R n n.
pose i:=@euclidean_first_injection_map R n n.
pose j:=@euclidean_last_injection_map R n n.
pose F:=fun z:V=>i (subspace_val z.1)+j (subspace_val z.2).
have hF:linear F.
  move=>c [x1 x2] [y1 y2].
  change (i (subspace_val (c*:x1+y1))+j (subspace_val (c*:x2+y2))=
    c*:(i (subspace_val x1)+j (subspace_val x2))+(i (subspace_val y1)+j (subspace_val y2))).
  by rewrite !linearP scalerDr addrACA.
pose L:=@HomMap R V P F (introT (asboolP _) hF).
have hpi y:p (i y)=y:=@euclidean_first_block_injectionK R n n y.
have hpj y:p (j y)=0:=@euclidean_first_block_last_injection R n n y.
have hqi y:q (i y)=0:=@euclidean_last_block_first_injection R n n y.
have hqj y:q (j y)=y:=@euclidean_last_block_injectionK R n n y.
have hLp z:p (L z)=subspace_val z.1.
  change (p (i (subspace_val z.1)+j (subspace_val z.2))=subspace_val z.1).
  by rewrite (linD (hom_linear p)) hpi hpj addr0.
have hLq z:q (L z)=subspace_val z.2.
  change (q (i (subspace_val z.1)+j (subspace_val z.2))=subspace_val z.2).
  by rewrite (linD (hom_linear q)) hqi hqj add0r.
have hLi:injective L.
  move=>[x1 x2] [y1 y2] he.
  have h1:subspace_val x1=subspace_val y1 by rewrite -(hLp (x1,x2)) -(hLp (y1,y2)) he.
  have h2:subspace_val x2=subspace_val y2 by rewrite -(hLq (x1,x2)) -(hLq (y1,y2)) he.
  have hx1:x1=y1:=subspace_val_injective h1.
  have hx2:x2=y2:=subspace_val_injective h2.
  by rewrite hx1 hx2.
have [z hz]:=grassmann_proof Z.
have [w hw]:=grassmann_proof W.
have hb:=@cartesian_basisP R ZX WX mu nu z w hz hw.
have hr:=@linear_injective_rank R V P (mu+nu) (@cartesian_basis R ZX WX mu nu z w) hb
  (n+n) (@coordinate_basis R (n+n)) (@coordinate_basisP R (n+n)) L hLi.
pose H:=@GrassmannSubspace R P (mu+nu) (range_subspace (hom_as_linear L)) hr.
exists H=>x; split.
- move=>[v he].
  change (x=L v) in he; rewrite he hLp hLq.
  split; exact: subspace_valP.
- move=>[hxZ hxW].
  exists (subspace_lift hxZ,subspace_lift hxW).
  change (x= i (subspace_val (subspace_lift hxZ))+j (subspace_val (subspace_lift hxW))).
  rewrite !subspace_liftE.
  exact (@euclidean_block_linear_decomposition R n n x).
Qed.
