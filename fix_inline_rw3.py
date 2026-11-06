import sys
path = "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM1_4.lean"
with open(path, "r") as f:
    content = f.read()

content = content.replace(
    "| error e =>\n              trace_state\n              rw [h_set_op] at h_sl",
    "| error e =>\n              simp only [Array.size_toArray, List.length, Nat.sub_self, Array.getElem_toArray, List.getElem_singleton, getElem] at h_sl\n              rw [h_set_op] at h_sl"
)
content = content.replace(
    "| ok frame_new =>\n              rw [h_set_op] at h_sl",
    "| ok frame_new =>\n              simp only [Array.size_toArray, List.length, Nat.sub_self, Array.getElem_toArray, List.getElem_singleton, getElem] at h_sl\n              rw [h_set_op] at h_sl"
)

with open(path, "w") as f:
    f.write(content)
