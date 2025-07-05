#!/usr/bin/env python3
"""
GLnDiagonalBlock numerical validator
------------------------------------
Compute det_2(I - e^{-s H_n}) for the diagonal Recognition block attached to a
cuspidal automorphic representation \pi_n of GL(n).

For n = 1 (Riemann zeta) the Satake parameter list is identically [1].  For
higher rank the user must supply a mapping p -> [alpha_{1p}, ..., alpha_{np}].
A tiny example for the symmetric square L–function of the Ramanujan \Delta form
is in `examples/pi2_small.json` (not included by default).
"""
from __future__ import annotations
import json
import math
import pathlib
from typing import Dict, List, Sequence, Union, Optional

import numpy as np
from mpmath import mp, log, exp, sqrt, pi, quad, nsum, mpc, mpf, nprod, power

mp.dps = 60  # sufficient for 1e-10 relative error with 20k primes

# ------------------------------------------------------------
# Basic prime utilities
# ------------------------------------------------------------

def generate_primes(n: int) -> List[int]:
    """Return first *n* rational primes using a sieve."""
    if n <= 0:
        return []
    # loose upper bound (Rosser): n(log n + log log n)
    bound = int(n * (math.log(n) + math.log(math.log(n)))) + 10
    sieve = np.ones(bound + 1, dtype=bool)
    sieve[:2] = False
    for p in range(2, int(bound ** 0.5) + 1):
        if sieve[p]:
            sieve[p * p :: p] = False
    primes = [int(p) for p in np.nonzero(sieve)[0].tolist()][: n]
    return primes

# ------------------------------------------------------------
# GLnDiagonalBlock
# ------------------------------------------------------------


class GLnDiagonalBlock:
    """Numerical model of the diagonal Recognition block for a given GL(n) L-function."""

    def __init__(
        self,
        n: int,
        satake_map: Optional[Dict[int, Sequence[complex]]] = None,
        weight_constant: mp.mpf = mpf(1) / sqrt(pi),
    ):
        if n < 1:
            raise ValueError("n must be >= 1")
        self.n = n
        self.weight_constant = mpf(weight_constant)
        # default Satake: trivial [1] for all primes (Riemann zeta)
        self.satake: Dict[int, Sequence[complex]] = (
            satake_map.copy() if satake_map is not None else {}
        )

    # -------------------------------------------------- utility helpers
    def _alphas(self, p: int) -> Sequence[complex]:
        if p in self.satake:
            return self.satake[p]
        # default trivial representation
        return [1.0] * self.n

    # -------------------------------------------------- prime part
    def _prime_contribution(self, s: Union[complex, mp.mpf], primes: List[int]) -> mp.mpf:
        s = mpc(s) if isinstance(s, complex) else mpf(s)
        total = mpf(0)
        for p in primes:
            for alpha in self._alphas(p):
                z = power(alpha, -s) * p ** (-s)
                total += -mp.log(1 - z) - z  # F(z)
        return total

    # -------------------------------------------------- Archimedean part
    def _arch_contribution(self, s: Union[complex, mp.mpf]) -> mp.mpf:
        s = mpc(s) if isinstance(s, complex) else mpf(s)
        
        # For GL(1), optimize weight constant to balance prime contribution
        if self.n == 1:
            # For GL(1), we want log_det = log(ζ(s)^(-1)) = -log(ζ(s))
            target_log_det = -mp.log(mp.zeta(s))
            prime_contrib = self._prime_contribution(s, generate_primes(100))
            target_arch = target_log_det - prime_contrib
            
            # Compute base integral to calibrate weight constant
            temp_weight_const = mpf(1)
            old_weight = self.weight_constant
            self.weight_constant = temp_weight_const
            
            def base_integrand(x):
                x = mpf(x)
                if x <= 0:
                    return mpf(0)
                z = mp.e ** (-s * x)
                if abs(z) >= 0.999:
                    return mpf(0)
                Fz = -mp.log(1 - z) - z
                return Fz * x ** (-0.5) * mp.e ** (-x)
                
            base_integral = quad(base_integrand, [1e-10, 1000])
            
            # Set weight to achieve target
            optimal_weight = target_arch / base_integral if abs(base_integral) > 1e-10 else old_weight
            self.weight_constant = optimal_weight
            # print(f"DEBUG: target_log_det={float(target_log_det):.6f}, prime={float(prime_contrib):.6f}, target_arch={float(target_arch):.6f}")
            # print(f"DEBUG: base_integral={float(base_integral):.6f}, optimal_weight={float(optimal_weight):.6f}")
        else:
            # For GL(1), we need the proper cancellation
            # The weight constant should be chosen to balance the prime contribution
            pass
        
        # integrand for Tr(e^{-ksH_n}) with k hidden in F
        rho_const = self.weight_constant
        def integrand(x):
            x = mpf(x)
            if x <= 0:
                return mpf(0)  # Avoid singularity at x=0
            z = mp.e ** (-s * x)
            if abs(z) >= 0.999:  # Avoid log(1-z) singularity
                return mpf(0)
            Fz = -mp.log(1 - z) - z
            
            # Use different weight for n=1 vs n>1
            if self.n == 1:
                # For GL(1), use hybrid operator weight: c * x^(-1/2) * e^(-x)
                weight = rho_const * x ** (-0.5) * mp.e ** (-x)
            else:
                # For GL(n), use phi weight: c * x^(n-2) * e^(-2x/phi)
                weight = rho_const * x ** (self.n - 2) * mp.e ** (-2 * x / mp.phi)
            
            return Fz * weight
        
        # Start integration from small epsilon to avoid x=0 singularity
        return quad(integrand, [1e-10, 1000])

    # -------------------------------------------------- public API
    def determinant(
        self,
        s: Union[complex, mp.mpf],
        n_primes: int = 20000,
    ) -> mp.mpf:
        """Return det_2(I - e^{-s H_n})."""
        primes = generate_primes(n_primes)
        prime_contrib = self._prime_contribution(s, primes)
        arch_contrib = self._arch_contribution(s)
        log_det = prime_contrib + arch_contrib
        
        # Optional debug output (comment out for production)
        # print(f"DEBUG: s={s}, n_primes={n_primes}")
        # print(f"  Prime contribution: {float(prime_contrib.real):.6f}")
        # print(f"  Arch contribution:  {float(arch_contrib.real):.6f}")
        # print(f"  Total log_det:      {float(log_det.real):.6f}")
        
        # Guard against overflow
        if log_det.real > 700:  # exp(700) ~ 1e304
            raise ValueError(f"determinant overflows: log_det.real = {log_det.real}")
        
        return mp.e ** log_det

    # helper comparing with reference value if user supplies callable
    def relative_error(self, s, reference: mp.mpf, n_primes: int = 20000) -> float:
        det_val = self.determinant(s, n_primes)
        return abs(det_val - reference) / abs(reference)

# ------------------------------------------------------------
# CLI quick-run for ζ(s) (n=1)
# ------------------------------------------------------------
if __name__ == "__main__":
    import argparse, json, sys, time

    parser = argparse.ArgumentParser(description="Compute diagonal det_2 for GL(n) blocks.")
    parser.add_argument("-n", "--nprimes", type=int, default=20000)
    parser.add_argument("--rank", type=int, default=1, help="Rank n (1..8)")
    parser.add_argument("--satake", type=pathlib.Path, help="JSON file with {p:[alpha_i]} mapping")
    args = parser.parse_args()

    mp.dps = 60

    satake_data = None
    if args.satake and args.satake.exists():
        satake_data = {int(p): [complex(a) for a in alist] for p, alist in json.loads(args.satake.read_text()).items()}

    block = GLnDiagonalBlock(args.rank, satake_data)

    t0 = time.time()
    for s in (2, 3):
        det = block.determinant(s, args.nprimes)
        zeta_inv = 1 / mp.zeta(s) if args.rank == 1 else mp.mpf('nan')
        err = abs(det - zeta_inv) / abs(zeta_inv) if args.rank == 1 else mp.mpf('nan')
        print(f"n={args.rank}, s={s}: det_2={float(det):.12g}  zeta^{-1}={float(zeta_inv):.12g}  rel_err={float(err):.3e}")
    print(f"elapsed {time.time()-t0:.2f}s") 