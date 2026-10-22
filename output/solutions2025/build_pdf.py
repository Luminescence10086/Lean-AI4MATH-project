from pathlib import Path
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.lib import colors
from reportlab.lib.styles import ParagraphStyle
from reportlab.lib.enums import TA_CENTER
from reportlab.platypus import SimpleDocTemplate, Paragraph, PageBreak
from reportlab.lib.pagesizes import A4
import re
OUT=Path(__file__).parent
for name,file in [('Body','times.ttf'),('Bold','timesbd.ttf'),('Italic','timesi.ttf'),('BoldItalic','timesbi.ttf')]:
    pdfmetrics.registerFont(TTFont(name,'C:/Windows/Fonts/'+file))
pdfmetrics.registerFontFamily('Body',normal='Body',bold='Bold',italic='Italic',boldItalic='BoldItalic')
pdfmetrics.registerFont(TTFont('MathSymbols','C:/Windows/Fonts/cambria.ttc',subfontIndex=1))
styles={
 'title':ParagraphStyle('title',fontName='Bold',fontSize=26,leading=32,textColor=colors.HexColor('#122C46'),spaceAfter=18),
 'sub':ParagraphStyle('sub',fontName='Italic',fontSize=14,leading=20,spaceAfter=16),
 'h':ParagraphStyle('h',fontName='Bold',fontSize=17,leading=22,textColor=colors.HexColor('#122C46'),spaceAfter=14),
 's':ParagraphStyle('s',fontName='Bold',fontSize=11.5,leading=16,spaceBefore=10,spaceAfter=6),
 'p':ParagraphStyle('p',fontName='Body',fontSize=11,leading=15.2,spaceAfter=8),
 'eq':ParagraphStyle('eq',fontName='Body',fontSize=11.5,leading=19,alignment=TA_CENTER,spaceBefore=5,spaceAfter=12),
 'small':ParagraphStyle('small',fontName='Body',fontSize=9.3,leading=12.7,spaceAfter=7),
 'note':ParagraphStyle('note',fontName='Body',fontSize=10,leading=14,borderColor=colors.HexColor('#CDD9E3'),borderWidth=.7,borderPadding=8,backColor=colors.HexColor('#F3F6F8'),spaceBefore=10,spaceAfter=13),
}
pages=[]
def page(title,blocks): pages.append([('h',title)]+blocks)

pages.append([
('title','2025 Mathematics Papers<br/>Independent Solutions'),
('sub','Computational &amp; Applied Mathematics<br/>Probability &amp; Statistics'),
('p','Solutions to all six applied-mathematics questions and all four probability/statistics questions in the supplied papers. The reasoning was developed independently; no answer keys or direct solutions were searched.'),
('note','<b>Important qualifications.</b> Statistics 1(b) is false as written. Statistics 2 has a false universal follow-up request. Statistics 4 cannot guarantee solutions on every sample. Explicit counterexamples are supplied, and the intended high-probability result in Statistics 4 is proved under a stated regularity assumption.'),
('p','The companion <b>Exam2025.lean</b> checks selected mathematical components. It is a <b>partial formalization</b>, not an end-to-end formal proof of all ten problems. The last page and COVERAGE.md identify the missing analytic, spectral and probability bridges. There are no proof placeholders or added axioms in the file.'),
('s','Reading guide'),
('p','Applied 1: optimized iteration and error constant.<br/>Applied 2: inverse spectral radius of a path matrix.<br/>Applied 3: associated Legendre interpolation and least squares.<br/>Applied 4: optimal approximation by principal components.<br/>Applied 5: maximum-norm and energy stability of a θ-scheme.<br/>Applied 6: a stiff ODE and three time-stepping methods.'),
('p','Statistics 1: exact coverage and the false minimax claim.<br/>Statistics 2: the observation model and counterexamples.<br/>Statistics 3: independent two-point cyclic variables.<br/>Statistics 4: root-existence obstruction and concentration proof.'),
('small','Conventions: σ &gt; 0; the intervals in Statistics 1(a) are closed. Φ denotes the standard normal CDF. Real associated Legendre interpolation nodes lie in (-1,1). Infinite-grid maximum norms mean suprema. All asymptotic statements concern n → ∞. Prepared 14 October 2026.')])

page('Applied 1 · Optimal multipoint iteration',[
('p','Let ξ be a simple root and suppose f is sufficiently smooth near ξ, for example C⁴. Put e = x - ξ and c₂ = f″(ξ)/(2f′(ξ)), c₃ = f‴(ξ)/(6f′(ξ)). We seek the highest order valid for a generic smooth f, rather than an exceptional function.'),
('eq','f(ξ+e)/f′(ξ) = e + c₂e² + c₃e³ + O(e⁴),<br/>f(x)/f′(x) = e - c₂e² + (2c₂²-2c₃)e³ + O(e⁴).'),
('p','If z = x - βf(x)/f′(x), then'),
('eq','z-ξ = (1-β)e + βc₂e² + O(e³),<br/>f′(z)/f′(ξ) = 1 + 2(1-β)c₂e<br/>+ [2βc₂² + 3(1-β)²c₃]e² + O(e³).'),
('p','Inverting the last series, multiplying by the series for f, and substituting into the iteration gives'),
('eq','e<sub>new</sub> = (1-α)e + α(1-2β)c₂e²<br/>- α[(2-8β+4β²)c₂² + (-2+6β-3β²)c₃]e³ + O(e⁴).'),
('p','The linear coefficient vanishes universally only if α = 1. With this value, the quadratic coefficient vanishes universally only if β = 1/2. Thus'),
('eq','<b>α = 1, β = 1/2,</b><br/>e<sub>new</sub> = (c₂²-c₃/4)e³ + O(e⁴).'),
('p','The method is locally of order at least three, and exactly three when c₂²-c₃/4 ≠ 0. The denominator remains nonzero near ξ since it tends to f′(ξ) ≠ 0. The error estimate gives local convergence from a sufficiently close starting point.'),
('p','No universal fourth order is possible: eliminating the first two terms has fixed both parameters, and f(ξ+e) = e+e² gives c₂ = 1, c₃ = 0 and cubic coefficient 1. Special functions can have higher order; a linear function is solved in one step.'),
('note','Lean verifies the coefficient optimization and the nonzero cubic example. The Taylor expansions, remainder estimates and local convergence argument are not formalized.')])

page('Applied 2 · Spectral radius of A⁻¹',[
('p','The matrix is the adjacency matrix of a path with eight vertices. For k = 1,…,8 put t<sub>k</sub> = kπ/9 and v<sup>(k)</sup><sub>j</sub> = sin(jt<sub>k</sub>), j = 1,…,8.'),
('eq','v<sup>(k)</sup><sub>0</sub> = v<sup>(k)</sup><sub>9</sub> = 0,<br/>v<sup>(k)</sup><sub>j-1</sub> + v<sup>(k)</sup><sub>j+1</sub> = 2cos(t<sub>k</sub>)v<sup>(k)</sup><sub>j</sub>.'),
('p','The boundary identities apply to the first and last rows. Therefore Av<sup>(k)</sup> = λ<sub>k</sub>v<sup>(k)</sup> with'),
('eq','λ<sub>k</sub> = 2cos(kπ/9),   k = 1,…,8.'),
('p','Every vector is nonzero, since its first entry is nonzero. Cosine is strictly decreasing on (0,π), so the eight eigenvalues are distinct and the vectors form a basis. None of the eigenvalues vanishes, since kπ/9 = π/2 would require k = 9/2.'),
('p','The eigenvalues of A⁻¹ are 1/λ<sub>k</sub>. The smallest absolute values of λ<sub>k</sub> occur at k = 4 and 5, the indices nearest 9/2, and equal 2cos(4π/9) = 2sin(π/18). Hence'),
('eq','<b>ρ(A⁻¹) = 1/[2sin(π/18)] ≈ 2.8793852416.</b>'),
('s','An independent algebra check'),
('p','For the r-vertex path let D<sub>r</sub>(t) = det(tI-A<sub>r</sub>). Expansion along the last row gives D₀ = 1, D₁ = t and D<sub>r</sub> = tD<sub>r-1</sub>-D<sub>r-2</sub>. Thus'),
('eq','D₈(t) = t⁸-7t⁶+15t⁴-10t²+1.'),
('p','In particular det A = 1. The Lean source additionally gives an explicit integer matrix B and verifies AB = BA = I entry by entry.'),
('note','Lean checks both inverse identities and the continuant expansion. The determinant interpretation, sine eigenbasis and spectral-radius minimization are not formalized.')])

page('Applied 3(a) · Interpolation',[
('p','Write q<sub>k</sub> = P′<sub>k</sub>. For -1 &lt; x &lt; 1,'),
('eq','P¹<sub>k</sub>(x) = -√(1-x²)q<sub>k</sub>(x).'),
('p','P<sub>k</sub> has degree k and leading coefficient L<sub>k</sub> = 2<sup>-k</sup>(2k)!/(k!)² ≠ 0. Thus q<sub>k</sub> has degree k-1 and leading coefficient kL<sub>k</sub>. The polynomials q₁,…,q<sub>N</sub> form a basis for polynomials of degree at most N-1.'),
('p','Suppose a is in the interpolation matrix kernel. At each distinct node x<sub>i</sub> ∈ (-1,1),'),
('eq','0 = ∑<sub>k=1</sub><super>N</super>a<sub>k</sub>P¹<sub>k</sub>(x<sub>i</sub>)<br/>= -√(1-x<sub>i</sub>²)∑<sub>k=1</sub><super>N</super>a<sub>k</sub>q<sub>k</sub>(x<sub>i</sub>).'),
('p','The square-root factor is nonzero. Hence q = ∑ a<sub>k</sub>q<sub>k</sub>, of degree at most N-1, vanishes at N distinct points. The polynomial root bound gives q = 0; basis independence gives a = 0. The square matrix therefore has trivial kernel and is nonsingular.'),
('s','Equivalent determinant formula'),
('p','The change from q₁,…,q<sub>N</sub> to monomials is triangular with diagonal kL<sub>k</sub>. Combining it with the Vandermonde determinant yields'),
('eq','det = (-1)<super>N</super>[∏<sub>i=1</sub><super>N</super>√(1-x<sub>i</sub>²)]<br/>× [∏<sub>k=1</sub><super>N</super>kL<sub>k</sub>][∏<sub>i&lt;j</sub>(x<sub>j</sub>-x<sub>i</sub>)],'),
('p','which is nonzero.'),
('note','Domain qualification: merely excluding ±1 does not define a real square root at arbitrary nodes outside [-1,1]. On the standard real domain the intended condition is x<sub>i</sub> ∈ (-1,1). A consistent complex interpretation outside this interval gives the same nonzero-factor argument over ℂ.'),
('small','Lean proves the polynomial root-count implication, but not the Legendre basis identification or determinant factorization.')])

page('Applied 3(b,c) · Least squares and parity',[
('p','Assume f ∈ L²([-1,1]). Set φ<sub>k</sub> = P¹<sub>k</sub>. Expanding the squared error gives'),
('eq','E(a) = ‖f‖²-2∑<sub>k</sub>a<sub>k</sub>b<sub>k</sub>+∑<sub>k,j</sub>a<sub>k</sub>M<sub>kj</sub>a<sub>j</sub>,<br/>M<sub>kj</sub> = ∫<sub>-1</sub><super>1</super>φ<sub>k</sub>φ<sub>j</sub> dx,   b<sub>k</sub> = ∫<sub>-1</sub><super>1</super>fφ<sub>k</sub> dx.'),
('p','The normal equations are Ma = b. If a ≠ 0, the polynomial ∑ a<sub>k</sub>P′<sub>k</sub> is nonzero, so its product with √(1-x²) is nonzero on an open interval. Therefore aᵀMa = ∫(∑ a<sub>k</sub>φ<sub>k</sub>)² &gt; 0. This proves positive definiteness and uniqueness.'),
('s','The matrix is actually diagonal'),
('p','The self-adjoint Legendre equation is ((1-x²)P′<sub>k</sub>)′ + k(k+1)P<sub>k</sub> = 0. Integrating by parts gives a zero endpoint term, and hence'),
('eq','M<sub>kj</sub> = ∫<sub>-1</sub><super>1</super>(1-x²)P′<sub>k</sub>P′<sub>j</sub> dx<br/>= k(k+1)∫<sub>-1</sub><super>1</super>P<sub>k</sub>P<sub>j</sub> dx<br/>= [2k(k+1)/(2k+1)]δ<sub>kj</sub>.'),
('p','For completeness, ordinary orthogonality follows by integrating Rodrigues’ formula P<sub>k</sub> = (2<sup>k</sup>k!)⁻¹ d<sup>k</sup>(x²-1)<sup>k</sup>/dx<sup>k</sup> against a lower-degree polynomial k times. All boundary terms vanish. For its squared norm, the same calculation gives (L<sub>k</sub>/2<sup>k</sup>)I<sub>k</sub>, where I<sub>k</sub> = ∫(1-x²)<sup>k</sup>dx. Integration by parts yields I<sub>k</sub> = 2kI<sub>k-1</sub>/(2k+1), I₀ = 2, and thus ‖P<sub>k</sub>‖² = 2/(2k+1). The differential equation follows from Rodrigues’ formula by differentiation.'),
('eq','<b>a<sub>k</sub> = [(2k+1)/(2k(k+1))]∫<sub>-1</sub><super>1</super>f(x)P¹<sub>k</sub>(x) dx.</b>'),
('p','For (c), P<sub>k</sub>(-x) = (-1)<super>k</super>P<sub>k</sub>(x) implies φ<sub>k</sub>(-x) = (-1)<super>k+1</super>φ<sub>k</sub>(x). When k+j is odd, φ<sub>k</sub>φ<sub>j</sub> is odd and its integral over [-1,1] is zero.'),
('small','Lean checks positive diagonal weights, diagonal-system algebra, and I = -I ⇒ I = 0. It does not identify the integrals with the diagonal weights.')])
page('Applied 4 · Optimal orthonormal vectors',[
('p','Let Y = [y₁ ··· y<sub>n</sub>] and C = YYᵀ = ∑ y<sub>j</sub>y<sub>j</sub>ᵀ. Fix ℓ ≤ dim V. Choose ψ₁,…,ψ<sub>ℓ</sub> as orthonormal eigenvectors of C for its ℓ largest eigenvalues, equivalently the first ℓ left singular vectors of Y.'),
('p','For any orthonormal family, P = ∑ ψ<sub>i</sub>ψ<sub>i</sub>ᵀ is an orthogonal projection. Pythagoras gives'),
('eq','J = ∑<sub>j</sub>‖y<sub>j</sub>‖² - ∑<sub>i=1</sub><super>ℓ</super>ψ<sub>i</sub>ᵀCψ<sub>i</sub>.'),
('p','Let u₁,…,u<sub>m</sub> be an orthonormal eigenbasis with λ₁ ≥ ··· ≥ λ<sub>m</sub> ≥ 0. Define w<sub>k</sub> = ∑<sub>i=1</sub><super>ℓ</super>(u<sub>k</sub>ᵀψ<sub>i</sub>)². Bessel’s inequality and orthonormality give'),
('eq','0 ≤ w<sub>k</sub> ≤ 1,   ∑<sub>k</sub>w<sub>k</sub> = ℓ,<br/>∑<sub>i</sub>ψ<sub>i</sub>ᵀCψ<sub>i</sub> = ∑<sub>k</sub>λ<sub>k</sub>w<sub>k</sub>.'),
('p','For ℓ ≥ 1, subtract λ<sub>ℓ</sub> times the mass identity. For k ≤ ℓ the remaining term is at most λ<sub>k</sub>-λ<sub>ℓ</sub>, because w<sub>k</sub> ≤ 1; for k &gt; ℓ it is nonpositive because w<sub>k</sub> ≥ 0. Therefore'),
('eq','∑<sub>k=1</sub><super>m</super>λ<sub>k</sub>w<sub>k</sub> ≤ ∑<sub>k=1</sub><super>ℓ</super>λ<sub>k</sub>.'),
('p','Equality holds for ψ<sub>i</sub> = u<sub>i</sub>. If r = rank Y = dim V and σ₁,…,σ<sub>r</sub> are the positive singular values in decreasing order, then'),
('eq','<b>J<sub>min</sub> = ∑<sub>k=ℓ+1</sub><super>r</super>λ<sub>k</sub> = ∑<sub>k=ℓ+1</sub><super>r</super>σ<sub>k</sub>².</b>'),
('p','For ℓ = 0 the value is ∑‖y<sub>j</sub>‖². If ℓ is free to choose as well, ℓ = r gives minimum zero. Repeated eigenvalues at the cutoff allow multiple optimal subspaces.'),
('p','For n much smaller than m, diagonalize YᵀY instead. If v<sub>i</sub> is a unit eigenvector with positive eigenvalue λ<sub>i</sub>, set ψ<sub>i</sub> = Yv<sub>i</sub>/√λ<sub>i</sub>.'),
('note','Lean verifies the spectral weight inequality. The spectral theorem, Bessel step and projection-error reduction are not formalized.')])

page('Applied 5(a) · Maximum-norm stability',[
('p','Set τ = Δt, h = Δx and r = τ/h². Interpret ‖U‖∞ as sup<sub>j∈ℤ</sub>|U<sub>j</sub>|: bounded sequences need not attain a maximum. The printed sampling formula u₀(jΔt) should be u₀(jΔx) for the intended spatial grid, but stability only uses bounded initial data.'),
('eq','[1+θτ+2θr]U<sup>m+1</sup><sub>j</sub> - θr(U<sup>m+1</sup><sub>j-1</sub>+U<sup>m+1</sup><sub>j+1</sub>)<br/>= [1-(1-θ)τ-2(1-θ)r]U<sup>m</sup><sub>j</sub><br/>+ (1-θ)r(U<sup>m</sup><sub>j-1</sub>+U<sup>m</sup><sub>j+1</sub>).'),
('p','A sufficient constant in the requested form is'),
('eq','<b>A(θ) = 1-θ.</b>'),
('p','Indeed, A(θ)τ ≤ h²/(4+h²) is (1-θ)(τ+4r) ≤ 1. This makes every right-hand coefficient nonnegative; their sum is 1-(1-θ)τ ≥ 0.'),
('s','Implicit inverse on the infinite grid'),
('p','Let S be the shift and a = 1+θτ+2θr. The left operator is L = aI-θr(S+S⁻¹). Since 2θr/a &lt; 1, it has the norm-convergent Neumann inverse'),
('eq','L⁻¹ = a⁻¹∑<sub>k=0</sub><super>∞</super>[θr(S+S⁻¹)/a]<super>k</super>.'),
('p','Every term preserves positivity, and ‖L⁻¹‖∞ ≤ 1/(a-2θr) = 1/(1+θτ). This establishes existence and uniqueness of each bounded step without assuming an attained maximum.'),
('p','The right operator R has ‖R‖∞ ≤ 1-(1-θ)τ. With q = [1-(1-θ)τ]/[1+θτ] ≥ 0, induction gives'),
('eq','‖U<sup>m+1</sup>‖∞ ≤ q‖U<sup>m</sup>‖∞,<br/><b>‖U<sup>m</sup>‖∞ ≤ q<super>m</super>‖U⁰‖∞.</b>'),
('p','The chosen restriction is sufficient, not claimed sharp. This positivity proof actually needs only (1-θ)(τ+2r) ≤ 1. At θ = 1 there is no step restriction and q = 1/(1+τ).'),
('note','Lean verifies stencil algebra and norm-bound induction. The operator construction and norm estimates are not formalized.')])

page('Applied 5(b) · ℓ² stability',[
('p','On square-summable sequences with inner product h∑ U<sub>j</sub>V<sub>j</sub>, put H = I-δ<sub>h</sub>². It is bounded and self-adjoint, and summation by parts gives'),
('eq','⟨HU,U⟩ = ‖U‖₂² + h∑<sub>j</sub>|(U<sub>j+1</sub>-U<sub>j</sub>)/h|² ≥ ‖U‖₂².'),
('p','The scheme is (I+θτH)U<sup>m+1</sup> = (I-(1-θ)τH)U<sup>m</sup>. The discrete Fourier transform, initially on finite sequences and then by density and Plancherel, turns H into multiplication by'),
('eq','λ(ω) = 1+4h⁻²sin²(ω/2),   -π ≤ ω ≤ π,<br/>1 ≤ λ(ω) ≤ 1+4h⁻².'),
('p','For z = τλ(ω) ≥ 0 the step factor is'),
('eq','g<sub>θ</sub>(z) = [1-(1-θ)z]/[1+θz].'),
('p','The denominator is positive. The upper inequality g ≤ 1 is automatic. The lower inequality g ≥ -1 is equivalent to'),
('eq','<b>(1-2θ)z ≤ 2.</b>'),
('p','For θ ∈ [1/2,1], this holds for all z ≥ 0, so Plancherel implies ‖U<sup>m</sup>‖₂ ≤ ‖U⁰‖₂ for arbitrary τ,h &gt; 0.'),
('p','For θ ∈ [0,1/2), require the inequality at the largest λ. This gives'),
('eq','(1-2θ)τ(1+4h⁻²) ≤ 2,<br/><b>B(θ) = 1-2θ,</b><br/><b>B(θ)Δt ≤ 2(Δx)²/[4+(Δx)²].</b>'),
('p','The condition is sharp for a uniform ℓ² contraction. At equality the endpoint factor can be -1, so only non-increase is claimed. If the condition fails, a frequency interval of positive measure has |g| &gt; 1; a Fourier transform supported there violates one-step contraction.'),
('note','Lean proves the scalar stability equivalence and unconditional θ ≥ 1/2 case. The Fourier and operator bridges are not formalized.')])

page('Applied 6(a,b) · Exact solution and explicit Euler',[
('s','(a) Exact solution'),
('p','The second equation gives y₂(t) = e<super>-t</super>. Using an integrating factor in the first gives'),
('eq','(e<super>1000t</super>y₁(t))′ = 999e<super>999t</super>,<br/><b>y₁(t) = e<super>-t</super>+e<super>-1000t</super>,   y₂(t) = e<super>-t</super>.</b>'),
('p','Differentiation and evaluation at zero verify the solution. The change a = y₁-y₂, b = y₂ diagonalizes the system: a′ = -1000a, b′ = -b, a(0) = b(0) = 1.'),
('s','(b) Explicit Euler'),
('p','For y′ = λy the factor is R(z) = 1+z. Its non-amplifying stability region is the closed disk'),
('eq','<b>{z ∈ ℂ : |1+z| ≤ 1}.</b>'),
('p','If absolute stability means asymptotic decay, use the open disk instead. Here the factors are 1-1000h and 1-h, so non-amplification requires 0 &lt; h ≤ 0.002; strict decay requires 0 &lt; h &lt; 0.002.'),
('eq','a<sub>m</sub> = (1-1000h)<super>m</super>,   b<sub>m</sub> = (1-h)<super>m</super>,<br/>y₁,<sub>m</sub> = a<sub>m</sub>+b<sub>m</sub>,   y₂,<sub>m</sub> = b<sub>m</sub>.'),
('p','For h &gt; 0.002, |1-1000h| &gt; 1, so |a<sub>m</sub>| → ∞. Since |y₁,<sub>m</sub>-y₂,<sub>m</sub>| ≤ √2‖y<sub>m</sub>‖₂, the vector norm diverges. The actual initial fast-mode coefficient is 1, so the unstable mode is present.'),
('p','At h = 0.002 the fast mode is (-1)<super>m</super>, bounded but nondecaying. Divergence here concerns fixed h and m → ∞, not a finite computation on a fixed time interval.'),
('note','Lean verifies the exact initial data and derivatives, the threshold and unstable factor, and an explicit modal recurrence. The unbounded-power limit is not formalized.')])

page('Applied 6(c,d) · Implicit Euler and trapezoidal rule',[
('s','(c) Implicit Euler'),
('p','R(z) = 1/(1-z). Its non-amplifying region {z : |1-z| ≥ 1} includes the closed left half-plane. For the system,'),
('eq','a<sub>m</sub> = (1+1000h)<super>-m</super>,   b<sub>m</sub> = (1+h)<super>-m</super>,<br/>y<sub>m</sub> = (a<sub>m</sub>+b<sub>m</sub>, b<sub>m</sub>)ᵀ.'),
('p','For every h &gt; 0 both factors lie strictly between 0 and 1. All solutions and initial perturbations decay in modal coordinates and hence in ℝ². This proves unconditional stability. Also R(z) → 0 on the negative real axis as z → -∞: implicit Euler is L-stable and strongly damps stiff modes.'),
('s','(d) Trapezoidal rule'),
('eq','R(z) = (1+z/2)/(1-z/2),<br/>|R(z)| ≤ 1 ⇔ |1+z/2|² ≤ |1-z/2|² ⇔ Re z ≤ 0.'),
('p','Its pole z = 2 is outside this region. Thus it is A-stable. The two factors for this system are'),
('eq','r<sub>f</sub> = (1-500h)/(1+500h),<br/>r<sub>s</sub> = (1-h/2)/(1+h/2),<br/>a<sub>m</sub> = r<sub>f</sub><super>m</super>,   b<sub>m</sub> = r<sub>s</sub><super>m</super>.'),
('p','Both have absolute value less than 1 for every h &gt; 0. Therefore all perturbations decay. However r<sub>f</sub> is negative for h &gt; 0.002, giving alternating fast-mode errors. For a very stiff mode r<sub>f</sub> is close to -1, so damping is poor.'),
('eq','R(z) → -1 as z → -∞: <b>not L-stable.</b>'),
('p','Stability means boundedness and decay of repeated steps. For a nonnormal system it need not imply contraction in every norm on each step; the fixed invertible modal transformation suffices.'),
('note','Lean proves the strict real-mode bounds. The complex regions and long-time limits are not formalized.')])

page('Statistics 1(a) · Exact coverage probability',[
('p','Assume c₁ &lt; c₂ and σ &gt; 0. X = 0 has probability zero. Replacing (X,μ) with (-X,-μ) preserves coverage, so for μ ≠ 0 use t = |μ|/σ &gt; 0. Let H<sub>t</sub>(c) = Φ(t(1/c-1)) for c ≠ 0.'),
('eq','<b>c₁c₂ &gt; 0:</b> H<sub>t</sub>(c₁)-H<sub>t</sub>(c₂),<br/><b>c₁ &lt; 0 &lt; c₂:</b> H<sub>t</sub>(c₁)+1-H<sub>t</sub>(c₂),<br/><b>c₁ = 0 &lt; c₂:</b> 1-H<sub>t</sub>(c₂),<br/><b>c₁ &lt; 0 = c₂:</b> H<sub>t</sub>(c₁).'),
('p','At μ = 0 the answer is'),
('eq','<b>1 if c₁ ≤ 0 ≤ c₂, and 0 otherwise.</b>'),
('s','Derivation'),
('p','For μ &gt; 0 and 0 &lt; c₁ &lt; c₂, coverage means μ/c₂ ≤ X ≤ μ/c₁; only X &gt; 0 contributes. Standardization gives H<sub>t</sub>(c₁)-H<sub>t</sub>(c₂).'),
('p','For c₁ &lt; c₂ &lt; 0, only X &lt; 0 contributes, but the event is again μ/c₂ ≤ X ≤ μ/c₁ and has the same expression. Reciprocals have this order on either half-line.'),
('p','For c₁ &lt; 0 &lt; c₂, coverage means X ≤ μ/c₁ or X ≥ μ/c₂, giving two disjoint tails. A zero lower endpoint removes the negative tail; a zero upper endpoint removes the positive tail.'),
('p','At μ = 0 and X ≠ 0, the random interval contains zero exactly when its coefficient interval contains zero. This is why substituting t = 0 into the nonzero-mean formulas is not generally valid; coverage can jump there.'),
('note','Lean checks reflection and the zero-mean interval event. Gaussian measures and the CDF evaluation are not formalized.')])
page('Statistics 1(b) · The printed assertion is false',[
('p','The expected-length identity cannot hold for arbitrary procedures F. Take F to output the deterministic interval (X-1,X+1). Its length is 2 for every sample, so its expected length equals 2 for every μ,σ.'),
('p','For a scale-form randomized interval with (C₁,C₂) drawn independently of X from a fixed G, set L = E<sub>G</sub>(C₂-C₁). Tonelli’s theorem gives'),
('eq','E<sub>μ,σ</sub>E<sub>G</sub>[(C₂-C₁)|X|] = L E<sub>μ,σ</sub>|X|.'),
('p','Matching the finite length 2 forces L to be finite. At μ = 0, X = σZ with Z standard normal, and E|X| = σ√(2/π). Thus the asserted identity for all parameters would require'),
('eq','Lσ√(2/π) = 2 for every σ &gt; 0.'),
('p','At σ = 1 and σ = 2 this gives L√(2/π) = 2 and 2L√(2/π) = 2, a contradiction. The length identity alone is impossible, regardless of the coverage inequality.'),
('s','Why an invariance theorem cannot be inserted silently'),
('p','The displayed supremum over F has no common length constraint. Moreover, the F in the second line is not bound by the first line’s supremum. A meaningful minimax statement needs a precisely specified procedure class, common scale-invariant length criterion or risk, and correct quantifiers.'),
('p','Different repairs give different theorems. The proper response to the printed universal assertion is therefore this counterexample, not an unprinted invariance claim.'),
('note','Lean checks the contradiction L·a = 2 and L·(2a) = 2. Tonelli factorization and the Gaussian absolute moment are not formalized.')])

page('Statistics 2 · Literal model and failed quantifiers',[
('p','The observation has law Q = (P₁+P₂)/2. Since E₁ν &gt; E₂ν, choosing population 1 is correct regardless of which population generated the observation. Thus'),
('eq','<b>P(correct) = Qφ = (1/2)∫φp₁ + (1/2)∫φp₂.</b>'),
('p','The expression (1/2)∫φp₁ + (1/2)∫(1-φ)p₂ would instead measure identification of the source population, a different task.'),
('s','The proposed universal guarantee is false'),
('p','Take ν(r)=r, P₁=N(1,1), P₂=N(0,1), and'),
('eq','φ<sub>-</sub>(r) = 1/4 + arctan(r)/(2π).'),
('p','The laws have Lebesgue densities and finite means 1 and 0; ν(X) and ν(Y) are unbounded. The rule is measurable and strictly increasing, hence injective. Since -π/2 &lt; arctan r &lt; π/2,'),
('eq','0 &lt; φ<sub>-</sub>(r) &lt; 1/2 for every r.'),
('p','Hence Qφ<sub>-</sub> &lt; 1/2. Strictness follows because the positive random variable 1/2-φ<sub>-</sub>(r) has strictly positive expectation.'),
('s','But a counterexample for every given φ is impossible'),
('p','The admissible injective rule'),
('eq','φ<sub>+</sub>(r) = 3/4 + arctan(r)/(2π)'),
('p','satisfies 1/2 &lt; φ<sub>+</sub>(r) &lt; 1 everywhere. Therefore Qφ<sub>+</sub> &gt; 1/2 for every pair of distributions, including all pairs with E₁ν &gt; E₂ν. No requested counterexample exists for this φ.'),
('p','Both conclusions matter: “always at least 1/2” is false, and the follow-up demand for a counterexample for every injective φ is also false. Injectivity does not force a range crossing 1/2 or symmetry under relabeling. The joint dependence of X and Y is irrelevant to a single mixture observation.'),
('note','Lean proves the strict pointwise bounds and injectivity of both rules. Mixture integration and the normal-law example are not formalized.')])

page('Statistics 3 · Explicit cyclic construction',[
('p','For n ≥ 2 set'),
('eq','t = π/(n+2),   q = 1/[4cos²t],   p = 1-q,<br/>a<sub>i</sub> = sin(it)/[2cos(t)sin((i+1)t)],   1 ≤ i ≤ n-1.'),
('p','Let X₀ = X<sub>n</sub> = 0 be constant. Independently for i=1,…,n-1, choose'),
('eq','X<sub>i</sub> = i-n with probability a<sub>i</sub>,<br/>X<sub>i</sub> = i with probability 1-a<sub>i</sub>.'),
('p','The next page proves 0 &lt; a<sub>i</sub> &lt; 1, a₁=q, a<sub>n-1</sub>=1-q, and (1-a<sub>i-1</sub>)a<sub>i</sub>=q. These make the construction valid on the finite product space {0,1}<sup>n-1</sup>. A constant is independent of every family, so X₁,…,X<sub>n</sub> are independent. X₀ is a second name for X<sub>n</sub>, not an additional independent variable.'),
('s','Endpoint comparisons'),
('eq','P(X₀ &lt; X₁) = 1-a₁ = 1-q,<br/>P(X<sub>n-1</sub> &lt; X<sub>n</sub>) = a<sub>n-1</sub> = 1-q.'),
('s','Interior comparisons'),
('p','For 2 ≤ k ≤ n-1, the two low faces increase from k-1-n to k-n and the two high faces increase from k-1 to k. A preceding low face is below a following high face. The only losing outcome is preceding high followed by low. Independence gives'),
('eq','P(X<sub>k-1</sub> ≥ X<sub>k</sub>) = (1-a<sub>k-1</sub>)a<sub>k</sub> = q,<br/><b>P(X<sub>k-1</sub> &lt; X<sub>k</sub>) = 1-q.</b>'),
('p','There are no ties. All n cyclic probabilities have the exact requested value.'),
('p','For n=2 there are no interior comparisons: X₁ takes -1 and 1 equally, and X₂=X₀=0, giving probability 1/2 in both directions. For n=3 the common winning probability is (√5-1)/2.'),
('note','Lean checks support order, the complete sine-ratio parameter identities, and finite-product normalization and rectangular independence. The final assembly into a cyclic random-variable existence theorem is not formalized.')])

page('Statistics 3 · Trigonometric verification',[
('p','We have 0 &lt; t ≤ π/4, so cos t &gt; 0. For 1 ≤ i ≤ n-1, all of it, (i+1)t and (i+2)t lie in (0,π), so their sines are positive.'),
('p','The addition identity gives'),
('eq','2cos(t)sin((i+1)t)-sin(it) = sin((i+2)t).'),
('p','Dividing by a positive denominator yields'),
('eq','1-a<sub>i</sub> = sin((i+2)t)/[2cos(t)sin((i+1)t)] &gt; 0.'),
('p','The definition also gives a<sub>i</sub> &gt; 0. Hence each two-point law is legitimate. For i=2,…,n-1,'),
('eq','(1-a<sub>i-1</sub>)a<sub>i</sub><br/>= [sin((i+1)t)/(2cos(t)sin(it))]<br/>× [sin(it)/(2cos(t)sin((i+1)t))]<br/>= 1/[4cos²t] = q.'),
('p','At the first endpoint, sin(2t)=2sin(t)cos(t) gives'),
('eq','a₁ = sin(t)/[2cos(t)sin(2t)] = q.'),
('p','At the last endpoint, (n+2)t=π implies sin((n-1)t)=sin(3t) and sin(nt)=sin(2t). Using sin(3t)=sin(t)(4cos²t-1),'),
('eq','a<sub>n-1</sub> = sin(3t)/[2cos(t)sin(2t)]<br/>= (4cos²t-1)/(4cos²t) = 1-q.'),
('p','This completes the construction without invoking an extremal-dice existence theorem.'),
('s','How the formula arises'),
('p','Increasing both low and high faces leaves one losing interior outcome. Requiring probability q forces the recurrence a<sub>i</sub> = q/(1-a<sub>i-1</sub>). The sine ratios solve it, and the endpoint requirement a<sub>n-1</sub> = 1-q selects t = π/(n+2).')])

page('Statistics 4 · Universal root existence fails',[
('p','Roots existing with high probability is different from a solution estimator existing on every sample, or almost surely. The latter fails even for a bounded C¹ score with globally bounded derivative.'),
('eq','ψ(x) = 1-(3/2)(1-x²)² for |x| ≤ 1;<br/>ψ(x) = 1 for |x| &gt; 1.'),
('p','This score lies in [-1/2,1]. Its derivative is 6x(1-x²) on (-1,1), and zero outside. Values and derivatives agree at ±1, so ψ is C¹ with bounded continuous derivative.'),
('p','Let R=1/4 with probability 512/675 and R=3 with probability 163/675. Then'),
('eq','ψ(1/4)=-163/512,   ψ(3)=1,<br/>Eψ(R)=0,<br/>ψ′(1/4)=45/32,   ψ′(3)=0,<br/><b>Eψ′(R)=16/15 ≠ 0.</b>'),
('p','Take p=1 and even n. On the event of exactly n/2 observations of each value, the score equation is'),
('eq','(n/2)[ψ(1/4-β)+ψ(3-β)] = 0.'),
('p','The arguments differ by 11/4 &gt; 2, so they cannot both belong to [-1,1]. One score is 1 and the other is at least -1/2. Their sum is at least 1/2 for every β, so the equation has no root.'),
('p','The event has probability binomial(n,n/2)(512/675)<sup>n/2</sup>(163/675)<sup>n/2</sup> &gt; 0 for every even n, while p log p/n=0. Thus almost-sure existence for each n does not follow from the assumptions.'),
('p','The event can be rare; this does not refute the intended high-probability existence statement. The next page proves that precise version.'),
('note','Lean proves the score bounds, mean-zero arithmetic, derivative-value arithmetic and positivity of the two-score sum for every β. The C¹ argument and event probability are not formalized.')])

page('Statistics 4 · The intended concentration result',[
('p','Write β* for the estimator (the β-hat in the paper). A precise valid conclusion is: with probability at least 1-2p/n, all p equations have roots with |β̂<sub>j</sub>| &lt; t<sub>n</sub> = √[p log n/(Bn)], for sufficiently large n. Estimators may be defined arbitrarily outside this good event; they need not solve the equations there.'),
('p','Assume ψ is globally differentiable with globally bounded derivative and is bounded. More generally, sample scores must be continuous and h(t)=Eψ(R-t) must satisfy h′(0)=-d. A derivative bound only near the point zero does not by itself justify differentiation under expectation for a general R.'),
('p','Let M=sup|ψ| &gt; 0. Replace ψ by -ψ if needed so that d &gt; 0. Dominated convergence in the difference quotient gives h(0)=0 and h′(0)=-d. Thus for all small t &gt; 0,'),
('eq','h(t) ≤ -dt/2,   h(-t) ≥ dt/2.'),
('p','Write m=n/p and S<sub>j</sub>(b)=m⁻¹∑ψ(R<sub>ij</sub>-b). Each summand lies in [-M,M]. One-sided Hoeffding gives'),
('eq','P(S<sub>j</sub>(t) ≥ 0) ≤ exp[-md²t²/(8M²)],<br/>P(S<sub>j</sub>(-t) ≤ 0) ≤ exp[-md²t²/(8M²)].'),
('p','Set B=d²/(8M²) and t=t<sub>n</sub>=√[log n/(Bm)]. Each bound equals 1/n. Taking the union over both signs and all cells yields'),
('eq','P(∃j: S<sub>j</sub>(-t<sub>n</sub>) ≤ 0 or S<sub>j</sub>(t<sub>n</sub>) ≥ 0) ≤ 2p/n.'),
('p','On the complementary event, continuity and the intermediate value theorem give roots strictly inside (-t<sub>n</sub>,t<sub>n</sub>). A measurable choice can be obtained from the boundary of the first negative excursion using rational arguments. Extend it by zero when the sign test fails. Then'),
('eq','<b>P(max<sub>j</sub>|β̂<sub>j</sub>| ≥ √[p log n/(Bn)]) ≤ 2p/n → 0.</b>'),
('p','The estimating equations are guaranteed only on the good event. Finally, the hypothesis is log p/m → 0. It forces m → ∞, since any bounded-m subsequence would have p=n/m → ∞. Consequently log n/m=(log p+log m)/m → 0 and p/n=1/m → 0, so t<sub>n</sub> → 0 as needed.'),
('small','Lean only verifies the scalar tail-bound multiplication. Hoeffding, measurable root selection, the limit argument and the complete high-probability theorem are not formalized.')])

page('Formal verification · Scope and reproducibility',[
('p','Exam2025.lean is a collection of checked components, not a complete translation of the PDF. Compiling it establishes only the stated theorems under their explicit hypotheses. An algebraic inequality alone is not a formal proof of the probability or operator theorem using it.'),
('s','Checked components'),
('p','Iteration: cancellation parameters and cubic coefficient.<br/>Path matrix: two exact inverse identities and continuant expansion.<br/>Legendre: root-count step, positive weights and diagonal system.<br/>Principal components: spectral weight inequality.<br/>θ-scheme: scalar stability, positive stencil and norm induction.<br/>Stiff ODE: exact derivatives and initial data, scalar factors and recurrence.<br/>Confidence interval: reflection, zero-mean event, length contradiction.<br/>Decision rules: arctangent bounds and injectivity.<br/>Cyclic variables: face comparisons, sine-ratio parameters, normalized finite products and rectangular independence.<br/>ANOVA: score bounds, mean identities and no-root algebra.'),
('s','Remaining formalization'),
('p','Taylor remainders and convergence; the sine eigenbasis and spectral radius; Legendre special-function and integral identities; spectral/projection reductions; infinite-grid operators and Fourier analysis; stability limits; Gaussian laws and CDFs; mixture integration; assembly of the cyclic random-variable existence theorem; score differentiability and probability of the ANOVA counterexample; Hoeffding and the complete root-existence theorem.'),
('s','Compiler and trust boundary'),
('p','The code uses the workspace’s pinned Lean 4.34.0-rc2 and Mathlib revision 85e3a25e006c35636f0e53b0e9296caca2685bc0. CHECK.ps1 invokes the installed compiler using the workspace package paths. verification.txt records the actual check result. There are no proof placeholders, added axioms or assumed exam answers used as proofs.'),
('p','Standard Lean/Mathlib classical foundations can include propext, Classical.choice and Quot.sound. No added axioms does not mean axiom-free foundations.'),
('note','Status: written solutions and counterexamples cover all ten questions. The requested complete Lean formalization is unfinished. The coverage record makes the missing work explicit and prevents a partial certificate from being mistaken for a complete one.')])

story=[]
for i,blocks in enumerate(pages):
    if i: story.append(PageBreak())
    for typ,text in blocks:
        text=text.replace('β̂','β<super>*</super>')
        text=''.join(('<font name="MathSymbols">'+c+'</font>') if c in '∈∃⇒⇔ℝℤℂ⟨⟩' else c for c in text)
        story.append(Paragraph(text,styles[typ]))
def footer(c,doc):
    w,h=A4
    c.setStrokeColor(colors.HexColor('#CCD6E0')); c.line(48,42,w-48,42)
    c.setFont('Body',8.5); c.setFillColor(colors.HexColor('#566575'))
    c.drawString(48,29,'2025 Mathematics | Independent solutions | Partial Lean formalization')
    c.drawRightString(w-48,29,str(doc.page))
pdf=OUT/'2025_Mathematics_Solutions.pdf'
doc=SimpleDocTemplate(str(pdf),pagesize=A4,rightMargin=48,leftMargin=48,topMargin=44,bottomMargin=54,title='2025 Mathematics: Independent Solutions',author='OpenAI Codex',pageCompression=1)
doc.build(story,onFirstPage=footer,onLaterPages=footer)
md=[]
for blocks in pages:
    for typ,text in blocks:
        plain=re.sub(r'<br\s*/?>','\n',text)
        plain=re.sub(r'<[^>]+>','',plain).replace('&lt;','<').replace('&gt;','>').replace('&amp;','&')
        md.append(('# ' if typ in ['h','title'] else '## ' if typ=='s' else '')+plain+'\n')
(OUT/'solutions_readable.txt').write_text('\n'.join(md),encoding='utf-8')
print(pdf.resolve()); print('Designed sections:',len(pages))
