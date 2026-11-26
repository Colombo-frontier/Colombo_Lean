import LeanArticleAudit.Prelude

/-!
Frozen source registry. Proof declarations live in the imported MinimaxAudit topic modules.
No theorem is considered audited until claim_mapping.json binds it
to an exact source claim and the external gate checks it.
-/

namespace LeanArticleAudit

/- Source record `eq:smoothness-definition` (definition, lines 220-234), source SHA-256 `bbc05b9dad44d8bc73d1dc2ac5faabcb0469fb5499e9282fe272cc6b65171f7a`.
Original: For fixed $L_p,D_Z>0$, let $\mathfrak S_p(L_p,D_Z)$ be the class of triples $(\cX,\cY,\phi)$ such that \begin{enumerate}[label=(\roman*),leftmargin=2.2em] \item $\cX\subseteq\R^{d_x}$ and $\cY\subseteq\R^{d_y}$ are nonempty compact convex sets with $\operatorname{diam}(\cX\times\cY)\le D_Z$; \item $\phi$ is defined and $p$ times continuously differentiable on a neighborhood of $\cX\times\cY$; \item $\phi(\cdot,y)$ is convex on $\cX$ for every $y\in\cY$; \item $\phi(x,\cdot)$ is concave on $\cY$ 
-/

/- Source record `definition-L243` (definition, lines 243-249), source SHA-256 `ef2216740d7d517d0ddc77d9205cbb48c165e4121027c3661ff3582cf330136d`.
Original: For each fixed choice of the public data, a deterministic $N$-query algorithm chooses each query $z_t\in\cZ$ as an arbitrary Borel measurable function of the transcript \[ (z_1,\cJ_p\phi(z_1),\ldots,z_{t-1},\cJ_p\phi(z_{t-1})). \] After at most $N$ queries it outputs an arbitrary Borel measurable transcript-dependent point $\widehat z\in\cZ$. The output need not have been queried. No linear-span, tensor-step, or update-rule restriction is imposed.
-/

/- Source record `definition-L251` (definition, lines 251-253), source SHA-256 `552af431f8ddb03570044f409380353c6366b98c5e4ec57dbed0975463e1676d`.
Original: A randomized $N$-query algorithm is a deterministic algorithm after drawing an independent internal random seed. For a fixed instance, its success probability is taken only over this seed. A lower-bound instance for a randomized algorithm must be fixed independently of the realized seed.
-/

/- Source record `lem:criteria` (lemma, lines 264-271), source SHA-256 `794ded693376e8d32818df8db929f89bda86cbe06e9d200d560057d4cef7d500`.
Original: \label{lem:criteria} For every admissible instance and every $z\in\cZ$, \begin{equation} \Gap_\phi(z)\le D_Z\rtan^\phi(z). \label{eq:criteria} \end{equation} If $\phi(x,y)=f(x)$, then $\Gap_\phi(x,y)=f(x)-\min_{u\in\cX}f(u)$, and one complete scalar $p$-jet of $\phi$ can be simulated with one $p$-jet of $f$.
-/

/- Source record `thm:main` (theorem, lines 286-334), source SHA-256 `575f2cd01377dea48eb1ea0b5ebef1bd8efaf4c07667fb724eb1f847f39f85c7`.
Original: \label{thm:main} For every fixed $p\ge2$, there are constants $a_p,b_p,C_p>0$ with the following property. Let $N\ge1$, $L_p>0$, and $D_Z>0$. \begin{enumerate}[label=(\roman*),leftmargin=2.2em] \item For every deterministic adaptive algorithm making at most $N$ feasible complete scalar $p$-jet queries, there are dimensions \[ d_x=d_y=2N+2, \] Euclidean balls $\cX\subseteq\R^{d_x}$ and $\cY\subseteq\R^{d_y}$ with $\operatorname{diam}(\cX\times\cY)=D_Z$, and a globally smooth convex--concave funct
-/

/- Source record `prop:upper` (proposition, lines 339-346), source SHA-256 `10622e52a7c66cb4868e16444b5fc14394cc0816e2e4971ba893c86f676520ec`.
Original: \label{prop:upper} For fixed $p\ge2$, there is a constant $C_p>0$ such that every known compact convex product $Z=X\times Y$ of diameter at most $D_Z$ admits a deterministic scalar-jet policy returning an evaluated $z\in Z$ and $n\in N_Z(z)$ with $\|F_\phi(z)+n\|\le\epsilon$ in at most \[ C_p\left(1+\left(\frac{L_pD_Z^p}{\epsilon}\right)^{2/(3p-1)}\right) \left[1+\log\left(3+\frac{L_pD_Z^p}{\epsilon}\right)\right]^{6(p-1)} \] queries. A saddle gap at most $\epsilon$ is attainable with the same b
-/

/- Source record `cor:complexity` (corollary, lines 366-375), source SHA-256 `65fef66e42e3430bcb9d645613343114c76406e6da811add8863000ee861ac6b`.
Original: \label{cor:complexity} Fix $p\ge2$. For $E\in\{\mathrm{tan},\mathrm{gap}\}$, let $Q_E=L_pD_Z^p/\epsilon$ when $E=\mathrm{tan}$ and $Q_E=L_pD_Z^{p+1}/\epsilon$ when $E=\mathrm{gap}$. There exist $c_p,C_p,Q_{0,p}>0$ such that, for $Q_E\ge Q_{0,p}$, \begin{equation}\label{eq:matching} c_pQ_E^{2/(3p-1)} \le T^{\mathrm{rand}}_{p,\mathrm{cc},E}(\epsilon) \le T^{\mathrm{det}}_{p,\mathrm{cc},E}(\epsilon) \le C_pQ_E^{2/(3p-1)}[1+\log(3+Q_E)]^{6(p-1)}. \end{equation} The upper inequality is inherited from
-/

/- Source record `lem:gate` (lemma, lines 410-466), source SHA-256 `145adc1a35c6613be918b64583ce6ae04dfdae3f048a7974f1c9b5f212283adf`.
Original: \label{lem:gate} For every fixed $p\ge2$, the following hold. \begin{enumerate}[label=(\alph*),leftmargin=2em] \item $h_\tau$ is odd, $H_\tau$ is even, and \[ h_\tau(s)=H_\tau(s)=0\qquad (|s|\le\tau/2). \] Moreover, \[ 0\le h_\tau'(s)\le1, \qquad |h_\tau(s)-s|\le\tau. \] \item If $|a|+|b|<\tau/2$, then $\Theta_\tau$ is identically zero on a neighborhood of $(a,b)$. If $|a|+|b|\le\tau/2$, its value and all derivatives vanish at $(a,b)$ by the smooth, flat cutoff. \item \[ \partial_b\Theta_\tau(a,
-/

/- Source record `lem:admissibility` (lemma, lines 588-596), source SHA-256 `03161496d8ead8d39293b2243aac7cda48da57409672f97e32838ab93a0e5ba9`.
Original: \label{lem:admissibility} The function \eqref{eq:hardpotential} is globally $\lambda(1-q)$-strongly convex in $x$ and globally $\lambda(1-q)$-strongly concave in $y$. The saddle operator has the same strong-monotonicity constant. Moreover, \[ \Lip(D^p\phi_{U,V}) \le \lambda C_p^{\rm sm}\tau^{1-p}, \] where $C_p^{\rm sm}$ depends only on $p$ and the fixed cutoff $\chi$.
-/

/- Source record `lem:saddlepoint` (lemma, lines 645-657), source SHA-256 `02e1ee11f5bdd23965c8068073e87e38ca39825959bbd7bc20e0f3697c40effe`.
Original: \label{lem:saddlepoint} The equation $r=T(r)$ has a unique solution $r^\star$ satisfying \[ |r_j^\star|\le c+2n\tau, \qquad j=1,\ldots,2n, \] and therefore \[ \|r^\star\|\le\sqrt{2n}(c+2n\tau). \] All inactive coordinates of the unique unconstrained saddle point are zero.
-/

/- Source record `lem:idealresidual` (lemma, lines 705-713), source SHA-256 `82bc89b6c65859b3585c6244ed4fdfadd78300b51222d3ed12b73fb38f7dd51e`.
Original: \label{lem:idealresidual} If $|r_n|\le\rho$, then \[ \|F_{\phi_0}(z)\| \ge \lambda\frac{q^{n-1}c-\rho}{\sqrt n}. \]
-/

/- Source record `lem:idealgap` (lemma, lines 756-776), source SHA-256 `1a9191f74b6af375b4b4b101530d6ed3a2b1d619b252e7ff4d5f0e8aefd6dfa5`.
Original: \label{lem:idealgap} Suppose $s=q^{n-1}c-r_n>0$. Put \[ \bar u=Uw, \qquad \bar v=Vw, \qquad \Delta_x=\frac{s}{\sqrt2}\bar u, \qquad \Delta_y=\frac{s}{\sqrt2}\bar v. \] Whenever $x+\Delta_x\in\cX$ and $y+\Delta_y\in\cY$, \begin{equation} \Gap_{\phi_0}(x,y) \ge \phi_0(x,y+\Delta_y)-\phi_0(x+\Delta_x,y) =\frac\lambda2s^2. \label{eq:exactgapwitness} \end{equation}
-/

/- Source record `lem:uniformapprox` (lemma, lines 806-818), source SHA-256 `ec0b7350536371dda76421d5a6656de74f5d58c481d7a36787aab5844c87ac0b`.
Original: \label{lem:uniformapprox} If $\|x\|,\|y\|\le R$, then \begin{equation} |\psi(W^Tz)-\psi_0(W^Tz)| \le 3\tau R\sqrt n. \label{eq:uniformapprox} \end{equation} Consequently, \[ |\phi(z)-\phi_0(z)|\le 3\lambda\tau R\sqrt n. \]
-/

/- Source record `lem:gatedresidual` (lemma, lines 835-844), source SHA-256 `265e4e7dfcabd4a4fb3da1ab94853a6ba7862ebf4ac49a3bed9212516467f27f`.
Original: \label{lem:gatedresidual} Let $e=W^TF_\phi(z)/\lambda$. If $|r_n|\le\rho$, then \begin{equation} \|F_\phi(z)\| \ge \lambda\frac{q^{n-1}c-\rho-n\tau}{\sqrt n}. \label{eq:gatedresidual} \end{equation}
-/

/- Source record `lem:normal` (lemma, lines 904-913), source SHA-256 `7bdc7501e88baea1deff6f63b7e3cec63a5d69ea273e6eee0d8c6736ff798935`.
Original: \label{lem:normal} Assume $|r_n|\le\tau$. Then \begin{equation} \rtan^\phi(z) \ge c_0\lambda\frac{c}{\sqrt n} \label{eq:tangentfinalscale} \end{equation} for a universal constant $c_0>0$.
-/

/- Source record `lem:gapfinal` (lemma, lines 942-950), source SHA-256 `3a88f5d0e417401b9c11fb1bba979b794cc6c7a77a402bed81867c4b0f8c972f`.
Original: \label{lem:gapfinal} Assume $|r_n|\le\tau$. Then \begin{equation} \Gap_\phi(z)\ge c_1\lambda c^2 \label{eq:gapfinalscale} \end{equation} for a universal constant $c_1>0$.
-/

/- Source record `prop:dettranscript` (proposition, lines 1016-1027), source SHA-256 `787f58613da348b16bb5423c37bbdf6a41567b3614e7dc5f2fdb63ed667e8a3d`.
Original: \label{prop:dettranscript} Let a deterministic algorithm make $N$ feasible queries and then output an arbitrary transcript-dependent point. In dimensions $d_x=d_y=2N+2$, one can choose $U,V$ online so that \begin{enumerate}[label=(\roman*),leftmargin=2em] \item every oracle answer is the complete scalar $p$-jet of the single final potential \eqref{eq:hardpotential}; and \item at the final output, \[ a_n=b_n=0. \] \end{enumerate}
-/

/- Source record `lem:haar` (lemma, lines 1049-1059), source SHA-256 `df012d17fbef0f84483777c1b16dc389ce37942d55ff6a80c28d8c4014392425`.
Original: \label{lem:haar} Let $U$ and $V$ be independent Haar orthonormal frames with $n\ge2$ columns in dimensions $d_x,d_y$, independent of a seed $\xi$. Set \[ \mathcal F_{t-1}=\sigma(\xi,u_1,\ldots,u_{t-1},v_1,\ldots,v_{t-1}). \] Suppose $(x_t,y_t)\in B_{d_x}(0,R)\times B_{d_y}(0,R)$ is $\mathcal F_{t-1}$-measurable for $1\le t\le n-1$, and the final output $(x_{\rm out},y_{\rm out})$ is $\mathcal F_{n-1}$-measurable and belongs to $B_{d_x}(0,R)\times B_{d_y}(0,R)$ almost surely. If $s>0$, $0<\delta<
-/

end LeanArticleAudit
