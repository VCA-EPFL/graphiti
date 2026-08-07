Keep lean proofs small and maintainable. This means:

1. Never remove or modify `#print axioms` statements, and always ensure they still pass.
2. Use `grind` and `simp` as much as possible.
3. Stay away from more manual tactics like `exact`.
