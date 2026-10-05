# Prescribed-support optimization

The paper proves Proposition 4 via a linear program. The formalization supplies a specialized solver with an explicit Boolean/list polynomial cost and global optimality over all real feasible vectors on the prescribed nonempty support.

For active coordinates, write `w_i = t + v_i * y_i`. The feasible increments have caps `min(1, t/(alpha*v_i)) - t/v_i` and total budget `K - t*sum_i(1/v_i)`. For a revenue threshold rho, optimization becomes continuous knapsack with scores `(r_i-rho)*v_i`. Positive-score coordinates are filled greedily in score order.

There are polynomially many score-order/sign changes. Within each score regime, the remaining dependence on t is piecewise affine; caps and budget changes yield a polynomial list of breakpoints. The solver enumerates the resulting rational candidates, reconstructs their vectors, and maximizes the exact fractional revenue.

`FixedSupportAlgorithmCorrect` proves feasibility, global optimality and positivity. `FixedSupportCostCertified` connects these properties to the actual raw bit-program output. `FixedSupportCostInputSize` and `FixedSupportCostSerializedInput` derive the polynomial from original stored fraction bits and encoding length. `FixedSupportAmbientPreprocess` pays for full catalogue traversal, mask validation, selection and positional reindexing.

The final `FixedSupportAmbient.ambient_prescribed_support_serialized` combines actual ambient execution, exact support, optimal value and serialized-input cost. `runAmbient_original_policy` supplies the original randomized MNL policy interpretation of that same output. The entry point takes structured raw fraction records and a Boolean mask; the FPTAS has a separate flat-bitstream parser/emitter theorem.
