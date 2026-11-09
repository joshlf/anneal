import LeanMiriSpec.Correspondence.CopyLM4_2

open MirSemantics

def my_eq_of_tag {e1 e2 : AllocMapEntry} {l : List AllocMapEntry} (h1 : e1 ∈ l) (h2 : e2 ∈ l) (ht : e1.tag = e2.tag) (hn : (l.map AllocMapEntry.tag).Nodup) : e1 = e2 := by
  sorry
