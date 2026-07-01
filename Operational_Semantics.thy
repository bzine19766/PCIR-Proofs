theory Operational_Semantics
  imports Configurations
begin

(* ========================================================================= *)
(* Section 1 : Operational Semantics                                         *)
(* ========================================================================= *)

text \<open>
The operational semantics of PCIR is expressed as an inductively defined
transition relation.

Each transition is labelled by an action.

The semantics is intentionally parameterized by the abstract predicate
prune. When prune is instantiated with True, the semantics corresponds
to the complete search procedure. Concrete pruning strategies can later
be introduced without changing the operational rules.
\<close>

inductive transition ::
  "graph \<Rightarrow> config \<Rightarrow> action \<Rightarrow> config \<Rightarrow> bool"
where

(* ------------------------------------------------------------------------- *)
(* Add Transition                                                            *)
(* ------------------------------------------------------------------------- *)

Add:
  "v \<in> C cfg \<Longrightarrow>
   prune
     (cfg\<lparr>
        I := I cfg \<union> {v},
        C := {u \<in> C cfg.
                u > v \<and>
                \<not> adjacent G u v}
      \<rparr>)
   \<Longrightarrow>
   transition
      G
      cfg
      (Add v)
      (cfg\<lparr>
         I := I cfg \<union> {v},
         C := {u \<in> C cfg.
                 u > v \<and>
                 \<not> adjacent G u v}
       \<rparr>)"

|

(* ------------------------------------------------------------------------- *)
(* Commit Transition                                                         *)
(* ------------------------------------------------------------------------- *)

Commit:
  "C cfg = {} \<Longrightarrow>
   I cfg \<noteq> {} \<Longrightarrow>
   maximal_independent G (P cfg) (I cfg) \<Longrightarrow>
   prune
     (cfg\<lparr>
        P := P cfg - I cfg,
        R := R cfg @ [I cfg],
        I := {},
        C := P cfg - I cfg
      \<rparr>)
   \<Longrightarrow>
   transition
      G
      cfg
      Commit
      (cfg\<lparr>
         P := P cfg - I cfg,
         R := R cfg @ [I cfg],
         I := {},
         C := P cfg - I cfg
       \<rparr>)"

(* ========================================================================= *)
(* Section 2 : Basic Elimination Rules                                       *)
(* ========================================================================= *)
(* ========================================================================= *)
(* Section 3 : Basic Semantic Properties                                     *)
(* ========================================================================= *)

lemma transition_action_cases:
  assumes
    "transition G cfg a cfg'"
  shows
    "(\<exists>v. a = Add v) \<or> a = Commit"
using assms
by (cases rule: transition.cases) auto






lemma transition_is_add_or_commit:
  assumes
    "transition G cfg a cfg'"
  obtains v
  where
    "a = Add v"
  |
    "a = Commit"
using assms
by (cases rule: transition.cases) auto




lemma add_transition_not_commit:
  assumes
    "transition G cfg (Add v) cfg'"
  shows
    "\<not> transition G cfg Commit cfg''"
proof
  assume
    "transition G cfg Commit cfg''"

  then have
    "C cfg = {}"
    by (cases rule: transition.cases) auto

  moreover

  from assms
  have
    "v \<in> C cfg"
    by (cases rule: transition.cases) auto

  ultimately
  show False
    by auto
qed




text \<open>
The following elimination rules are generated automatically by Isabelle.

transition.cases
transition.induct

They are intentionally not reproved here. They will be used in the next
theory to derive computational inversion lemmas.
\<close>

end