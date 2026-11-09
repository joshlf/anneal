with open("replacement.lean", "r") as f:
    content = f.read()

# Fix rfl in hiter0
rfl_fix = """            · have hff : (false = true) = false := rfl
              simp only [hff, ite_false]"""
content = content.replace("            · rfl\n", rfl_fix + "\n")

# Use dsimp to reduce collectChunksAux
simp_fix = """    dsimp
    simp only [hiter0, bind, Except.bind, pure, Except.pure, Array.append_empty, Id.pure, Id.bind]
    dsimp
    simp only [hiter1, bind, Except.bind, pure, Except.pure, Array.append_empty]
    rw [ht]
    rfl"""
content = content.replace("""    simp only [hiter0, bind, Except.bind, pure, Except.pure, Array.append_empty, Id.pure, Id.bind]
    simp only [hiter1, bind, Except.bind, pure, Except.pure, Array.append_empty]
    rw [ht]
    rfl""", simp_fix)

with open("replacement.lean", "w") as f:
    f.write(content)
