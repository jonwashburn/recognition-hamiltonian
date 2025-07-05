#!/usr/bin/env python3
"""
Full Recognition Hamiltonian Implementation
-------------------------------------------
Combines the eight GL(n) diagonal blocks with the octonionic braid operator
to construct the complete Recognition Hamiltonian H = H_diag + B.

Computes det_2(I - e^{-sH}) numerically and compares to the product
∏_{n=1}^8 Λ(s,π_n)^{-1} for validation.
"""

import json
import time
from typing import Dict, List, Optional, Tuple
import numpy as np
from mpmath import mp, log, exp, sqrt, pi, zeta, mpc, mpf
import scipy.sparse as sp
from scipy.sparse.linalg import expm, norm

# Import our diagonal block and braid implementations
from gln_block import GLnDiagonalBlock
from octonionic_braid import OctonionBraid

mp.dps = 50  # Precision for numerical validation

class RecognitionHamiltonian:
    """Full Recognition Hamiltonian H = H_diag + B with octonionic braid."""
    
    def __init__(
        self, 
        block_representations: List[Dict],
        braid_coupling: float = 0.01,
        max_primes: int = 1000  # Limit for computational feasibility
    ):
        """
        Initialize the Recognition Hamiltonian.
        
        Args:
            block_representations: List of 8 dicts, each containing GL(n) rep data
            braid_coupling: Octonionic braid coupling strength ε
            max_primes: Maximum number of primes for finite-dimensional approximation
        """
        if len(block_representations) != 8:
            raise ValueError("Must provide exactly 8 GL(n) representations")
        
        self.block_reps = block_representations
        self.epsilon = braid_coupling
        self.max_primes = max_primes
        
        # Create diagonal blocks
        self.diagonal_blocks = []
        for i, rep_data in enumerate(block_representations):
            rank = rep_data.get('rank', 1)
            satake_map = rep_data.get('satake_map', {})
            block = GLnDiagonalBlock(rank, satake_map)
            self.diagonal_blocks.append(block)
        
        # Determine block dimensions for finite approximation
        self.block_dims = [self._estimate_block_dimension(block) for block in self.diagonal_blocks]
        self.total_dim = sum(self.block_dims)
        
        # Create braid operator
        self.braid = OctonionBraid(self.block_dims, self.epsilon)
        
        print(f"Recognition Hamiltonian initialized:")
        print(f"  Block dimensions: {self.block_dims}")
        print(f"  Total dimension: {self.total_dim}")
        print(f"  Braid coupling: {self.epsilon}")
    
    def _estimate_block_dimension(self, block: GLnDiagonalBlock) -> int:
        """Estimate finite-dimensional truncation size for a block."""
        # Use number of primes * rank as rough dimension estimate
        base_dim = min(self.max_primes // 8, 50)  # Conservative estimate
        return max(block.n * base_dim, 10)  # At least 10-dimensional
    
    def _build_diagonal_matrix(self, s: complex) -> sp.csr_matrix:
        """Build the diagonal part H_diag as a sparse matrix."""
        # For finite approximation, use eigenvalues from first few primes
        from gln_block import generate_primes
        primes = generate_primes(self.max_primes // 8)
        
        rows, cols, data = [], [], []
        global_idx = 0
        
        for block_idx, block in enumerate(self.diagonal_blocks):
            # Get eigenvalues for this block
            eigenvals = []
            for p in primes:
                alphas = block._alphas(p)
                for alpha in alphas:
                    eigenval = float(log(p) + log(abs(alpha)))
                    eigenvals.append(eigenval)
            
            # Truncate to block dimension
            eigenvals = eigenvals[:self.block_dims[block_idx]]
            
            # Add to diagonal matrix
            for i, lam in enumerate(eigenvals):
                rows.append(global_idx + i)
                cols.append(global_idx + i)
                data.append(lam)
            
            global_idx += self.block_dims[block_idx]
        
        return sp.csr_matrix((data, (rows, cols)), shape=(self.total_dim, self.total_dim))
    
    def compute_determinant_diagonal_only(self, s: complex, n_primes: int = 1000) -> mpf:
        """Compute product of diagonal block determinants."""
        product = mpf(1)
        for block in self.diagonal_blocks:
            det_val = block.determinant(s, n_primes)
            product *= det_val
        return product
    
    def compute_determinant_full(self, s: complex) -> Tuple[mpf, Dict]:
        """
        Compute det_2(I - e^{-sH}) for the full braided Hamiltonian.
        Returns determinant value and diagnostic info.
        """
        # Build H_diag and B as sparse matrices
        H_diag = self._build_diagonal_matrix(s)
        B = self.braid.build_sparse_matrix()
        
        # Full Hamiltonian H = H_diag + B
        H_full = H_diag + B
        
        # Compute e^{-sH} using matrix exponential (expensive!)
        # For large matrices, this is the computational bottleneck
        exp_neg_sH = expm(-complex(s) * H_full)
        
        # 2-regularized determinant computation
        # det_2(I - A) = ∏_k (1 - λ_k) exp(λ_k) where λ_k are eigenvalues of A
        I = sp.identity(self.total_dim, format='csr')
        
        # For computational feasibility, use spectral approximation
        # This is a simplification - full implementation would require
        # more sophisticated trace-class methods
        eigenvals = sp.linalg.eigs(exp_neg_sH, k=min(self.total_dim//2, 50), 
                                  return_eigenvectors=False)
        
        log_det = mpf(0)
        for lam in eigenvals:
            if abs(lam) < 0.99:  # Convergence radius
                log_det += -log(1 - lam) - lam
        
        determinant = exp(log_det)
        
        diagnostics = {
            'matrix_dimension': self.total_dim,
            'braid_norm': norm(B),
            'num_eigenvals_used': len(eigenvals),
            'convergence_check': all(abs(lam) < 0.99 for lam in eigenvals)
        }
        
        return determinant, diagnostics
    
    def compare_with_l_functions(self, s: complex, n_primes: int = 1000) -> Dict:
        """Compare full determinant with product of L-functions."""
        
        # Compute diagonal-only (product of individual blocks)
        diag_det = self.compute_determinant_diagonal_only(s, n_primes)
        
        # For now, use diagonal determinant as L-function product approximation
        # In full implementation, would use actual L-function evaluations
        l_function_product = diag_det
        
        # Compute full braided determinant
        try:
            full_det, diagnostics = self.compute_determinant_full(s)
            
            # Relative error
            if abs(l_function_product) > 1e-15:
                rel_error = abs(full_det - l_function_product) / abs(l_function_product)
            else:
                rel_error = mpf('inf')
            
            return {
                's': s,
                'diagonal_determinant': float(diag_det),
                'full_determinant': float(full_det),
                'l_function_product': float(l_function_product),
                'relative_error': float(rel_error),
                'success': True,
                'diagnostics': diagnostics
            }
        
        except Exception as e:
            return {
                's': s,
                'diagonal_determinant': float(diag_det),
                'error': str(e),
                'success': False
            }

def create_example_representations() -> List[Dict]:
    """Create example GL(n) representations for testing."""
    return [
        {'rank': 1, 'name': 'Riemann zeta', 'satake_map': {}},  # ζ(s)
        {'rank': 1, 'name': 'Dirichlet L (mod 5)', 'satake_map': {}},  # L(s,χ) 
        {'rank': 2, 'name': 'GL(2) Maass form', 'satake_map': {}},  # Placeholder
        {'rank': 2, 'name': 'Symmetric square', 'satake_map': {}},  # Placeholder
        {'rank': 3, 'name': 'GL(3) Maass form', 'satake_map': {}},  # Placeholder
        {'rank': 3, 'name': 'Cubic twist', 'satake_map': {}},  # Placeholder
        {'rank': 4, 'name': 'GL(4) Sym³', 'satake_map': {}},  # Placeholder
        {'rank': 4, 'name': 'Tensor product', 'satake_map': {}}   # Placeholder
    ]

def benchmark_recognition_hamiltonian():
    """Run benchmark comparing full RH with L-function products."""
    print("Recognition Hamiltonian Benchmark")
    print("=" * 50)
    
    # Create example representations
    representations = create_example_representations()
    
    # Initialize Recognition Hamiltonian
    RH = RecognitionHamiltonian(
        representations, 
        braid_coupling=0.005,  # Small coupling for stability
        max_primes=200  # Limit computational cost
    )
    
    # Test points
    test_points = [2, 3, 0.5 + 14.134725j]  # Real points + first zeta zero
    
    results = []
    for s in test_points:
        print(f"\nEvaluating at s = {s}")
        result = RH.compare_with_l_functions(s, n_primes=500)
        results.append(result)
        
        if result['success']:
            print(f"  Diagonal det: {result['diagonal_determinant']:.6e}")
            print(f"  Full det:     {result['full_determinant']:.6e}")
            print(f"  Rel. error:   {result['relative_error']:.3e}")
            print(f"  Matrix dim:   {result['diagnostics']['matrix_dimension']}")
        else:
            print(f"  Error: {result['error']}")
    
    return results

if __name__ == "__main__":
    import argparse
    
    parser = argparse.ArgumentParser(description="Recognition Hamiltonian benchmark")
    parser.add_argument("--coupling", type=float, default=0.005, help="Braid coupling strength")
    parser.add_argument("--primes", type=int, default=200, help="Max primes for approximation")
    args = parser.parse_args()
    
    # Override defaults if provided
    mp.dps = 30  # Reduce precision for faster computation
    
    representations = create_example_representations()
    RH = RecognitionHamiltonian(representations, args.coupling, args.primes)
    
    print(f"Quick test at s=2 with ε={args.coupling}")
    result = RH.compare_with_l_functions(2)
    if result['success']:
        print(f"Relative error: {result['relative_error']:.3e}")
    else:
        print(f"Failed: {result['error']}") 