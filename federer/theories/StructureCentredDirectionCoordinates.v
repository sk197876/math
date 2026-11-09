(** Federer (1969), 3.3.4, pp. 290–291: regularity and puncture
    laws of the actual projected centred coordinates. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanRectangularMapContinuity EuclideanAdditiveGroup
  BorelFunctionUP BorelFunctionBasic StructureDirectionMapUP StructureDirectionMapExistence
  StructureDirectionDomain StructureProjectiveSpace TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_centred_linear_coordinates_continuous]:
    supporting the actual map q in Federer 3.3.4, pp. 290–291.
    Every original linear coordinate map composed with subtraction of
    the original centre is continuous in the existing Euclidean metrics. *)
Theorem structure_centred_linear_coordinates_continuous (R:realType) n d
    (L:Hom (R_n R n) (R_n R d))
    (a:inner_metric_space (@euclidean_inner_productP R n)):
  continuous (fun x:inner_metric_space (@euclidean_inner_productP R n)=>
    (L (x-a):inner_metric_space (@euclidean_inner_productP R d))).
Proof.
have hShift:continuous (fun x:inner_metric_space (@euclidean_inner_productP R n)=>x-a).
  have hEq:(fun x:inner_metric_space (@euclidean_inner_productP R n)=>x-a)=euclidean_translation (-a).
    by apply:funext=>x; rewrite /euclidean_translation addrC.
  by rewrite hEq; exact:euclidean_translation_continuous.
move=>x; exact (@continuous_comp
  (inner_metric_space (@euclidean_inner_productP R n))
  (inner_metric_space (@euclidean_inner_productP R n))
  (inner_metric_space (@euclidean_inner_productP R d))
  (fun y=>y-a) (fun u=>L u) x (hShift x) (@euclidean_rectangular_map_continuous R n d L (x-a))).
Qed.

(** Source for [structure_centred_direction_map_exists]: the actual
    local Borel direction map and its Borel nonzero domain in Federer
    3.3.4, pp. 290–291. The domain excludes the original centre;
    no puncture condition or regularity premise is added externally. *)
Theorem structure_centred_direction_map_exists (R:realType) n m
    (L:Hom (R_n R n) (R_n R m.+1))
    (a:inner_metric_space (@euclidean_inner_productP R n)):
  exists f:inner_metric_space (@euclidean_inner_productP R n)->structure_projective_space R m,
    is_structure_projective_direction_map
      (fun x:inner_metric_space (@euclidean_inner_productP R n)=>L (x-a)) f /\
    borel_set [set x:inner_metric_space (@euclidean_inner_productP R n)|
      0<inner_norm (@euclidean_inner_productP R m.+1) (L (x-a))] /\
    forall x,0<inner_norm (@euclidean_inner_productP R m.+1) (L (x-a)) ->x!=a.
Proof.
have hBorel:=continuous_borel_function (@structure_centred_linear_coordinates_continuous R n m.+1 L a).
have [f hF]:=structure_projective_direction_map_exists hBorel.
exists f; split=>//; split; first exact:structure_projective_direction_domain_borel hBorel.
move=>x hx; apply/eqP=>hEqual.
have hZero:L 0=0:=linear0 (hom_as_linear L).
by move:hx; rewrite hEqual subrr hZero inner_norm0 ltxx.
Qed.
