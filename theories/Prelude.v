From stdpp Require Export gmap sets fin_sets fin_map_dom.
From Corelib Require Export Program.Wf.
From Hammer Require Export Hammer.


(** All files open a Section parameterizing over:
      [Var]   : countable type of program variables
      [Value] : type of runtime values (needs EqDecision for map lookups)
    These are introduced in each file's own Section. *)
