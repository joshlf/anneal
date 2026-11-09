with open("replacement.lean", "r") as f:
    content = f.read()

# Fix hiter0's if false = true
content = content.replace("""            · have hff : (false = true) = false := rfl
              simp only [hff, ite_false]""", """            · split
              · contradiction
              · rfl""")

with open("replacement.lean", "w") as f:
    f.write(content)
