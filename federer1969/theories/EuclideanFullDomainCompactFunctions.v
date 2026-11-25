(** Federer (1969), 4.1.18, p. 375: the
    original compact scalar tests on R^n and on
    its full current-domain copy are exactly the
    same functions under the canonical inverse inclusions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals topology.
From Federer Require Import RealMetricBackground RealNormUP NormMetric InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentDomain EuclideanFullDomainMeasure
  IsotropyGroupTopology CompactSupportFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section EuclideanFullDomainCompactFunctions.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation XT:=(real_norm_metric_space
  (inner_norm_real_norm (@euclidean_inner_productP R n))).
Local Notation FT:=(current_domain R n (fun _=>True)).
Local Notation point:=(@euclidean_full_domain_point R n).

(** Source for [euclidean_full_domain_point_continuous]:
    the actual inverse inclusion is continuous,
    supporting the original compact tests and variation
    measures in Federer 4.1.18, p. 375. *)
Lemma euclidean_full_domain_point_continuous:
  continuous (fun x:XT=>(point x:FT)).
Proof.
apply:(@set_type_continuous_into XT (fun _=>True) XT point).
by move=>x;exact:cvg_id.
Qed.

(** Source for [euclidean_full_compact_function_pullback]:
    every original ambient compact scalar test is
    an original full-current-domain compact test,
    supporting 4.1.18, p. 375. *)
Theorem euclidean_full_compact_function_pullback (f:XT->R):
  compactly_supported_continuous_functions f ->
  compactly_supported_continuous_functions (fun x:FT=>f (set_val x)).
Proof.
move=>hF;split.
- move=>x;apply:(@continuous_comp FT XT (real_line_metric R) set_val f x).
  + exact:(@set_type_val_continuous XT (fun _=>True) x).
  + exact:hF.1.
- pose C:set FT:=set_val @^-1` real_function_support f.
  have hC:compact C:=@set_type_compact_preimage XT (fun _=>True)
    (real_function_support f) hF.2 (fun _ _=>Logic.I).
  have hClosed:closed C.
    apply:preimage_closed (@real_function_support_closed R XT f)=>x _.
    exact:(@set_type_val_continuous XT (fun _=>True) x).
  apply:(@real_function_compact_support_in_closed_set R FT
    (fun x:FT=>f (set_val x)) C hC hClosed)=>x hx.
  exact:real_function_zero_off_support hx.
Qed.

(** Source for [euclidean_full_compact_function_extension]:
    every original compact scalar test on the full
    current domain is an ambient compact scalar test,
    supporting 4.1.18, p. 375. No point in
    an empty open target is selected. *)
Theorem euclidean_full_compact_function_extension (f:FT->R):
  compactly_supported_continuous_functions f ->
  compactly_supported_continuous_functions (fun x:XT=>f (point x)).
Proof.
move=>hF;split.
- move=>x;apply:(@continuous_comp XT FT (real_line_metric R) point f x).
  + exact:(@euclidean_full_domain_point_continuous x).
  + exact:hF.1.
- pose C:set XT:=set_val @` real_function_support f.
  have hC:compact C.
    apply:continuous_compact hF.2.
    exact:continuous_subspaceT (@set_type_val_continuous XT (fun _=>True)).
  have hClosed:closed C:=compact_closed (@metric_hausdorff R XT) hC.
  apply:(@real_function_compact_support_in_closed_set R XT
    (fun x:XT=>f (point x)) C hC hClosed)=>x hx.
  apply:real_function_zero_off_support=>hSupport.
  apply:hx;exists (point x);by [].
Qed.
End EuclideanFullDomainCompactFunctions.
