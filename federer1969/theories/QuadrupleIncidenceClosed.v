(** Supporting Federer (1969), 3.4.8(5), p. 328:
    closed coordinate membership and open nonmembership
    conditions in the four-factor germ incidence space.
    This uses only product topology and continuous
    preimages of the original closed sets. *)
From mathcomp Require Import all_boot all_order boolp classical_sets topology.
From Federer Require Import TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [quadruple_incidence_closed_open]: three
    closed coordinate conditions and a fourth open
    nonmembership condition retain those topological
    properties, supporting 3.4.8(5), p. 328. *)
Lemma quadruple_incidence_closed_open (T:topologicalType) (A B C D:set T):
  closed A ->closed B ->closed C ->closed D ->
  @closed ((T*T)*(T*T))%type [set z|A z.1.1 /\B z.1.2 /\C z.2.1] /\
  @open ((T*T)*(T*T))%type [set z|~D z.2.2].
Proof.
move=>hA hB hC hD.
pose Z:=((T*T)*(T*T))%type.
have h1:continuous (fun z:Z=>z.1.1).
  move=>z;exact:(continuous_comp (@first_projection_continuous (T*T)%type (T*T)%type z)
    (@first_projection_continuous T T z.1)).
have h2:continuous (fun z:Z=>z.1.2).
  move=>z;exact:(continuous_comp (@first_projection_continuous (T*T)%type (T*T)%type z)
    (@second_projection_continuous T T z.1)).
have h3:continuous (fun z:Z=>z.2.1).
  move=>z;exact:(continuous_comp (@second_projection_continuous (T*T)%type (T*T)%type z)
    (@first_projection_continuous T T z.2)).
have h4:continuous (fun z:Z=>z.2.2).
  move=>z;exact:(continuous_comp (@second_projection_continuous (T*T)%type (T*T)%type z)
    (@second_projection_continuous T T z.2)).
have hPre1:@closed Z ((fun z:Z=>z.1.1) @^-1` A).
  exact:((@continuous_closedP Z T (fun z=>z.1.1)).1 h1 A hA).
have hPre2:@closed Z ((fun z:Z=>z.1.2) @^-1` B).
  exact:((@continuous_closedP Z T (fun z=>z.1.2)).1 h2 B hB).
have hPre3:@closed Z ((fun z:Z=>z.2.1) @^-1` C).
  exact:((@continuous_closedP Z T (fun z=>z.2.1)).1 h3 C hC).
have hPre4:@closed Z ((fun z:Z=>z.2.2) @^-1` D).
  exact:((@continuous_closedP Z T (fun z=>z.2.2)).1 h4 D hD).
split.
- exact:(closedI hPre1 (closedI hPre2 hPre3)).
- exact:(closed_openC hPre4).
Qed.
