# Lecture Hall：多项式性基线与 SAGBI 扩展

新增 [Lean 形式化补充](FORMALIZATION.md)：在实际有理系数多项式的分式域中，证明全部正下标定义方程存在唯一解，且每一项都有精确前缀变量的整数多项式见证。原文方阵列集和第四项的解释限制保持；Dyck 精确识别、composition 及 SAGBI 扩展仍依各自文字证明。

本版保留更正后的 v0.1.1 多项式性证明 `main.tex/main.pdf`，并增加 [扩展论文](extensions/LectureHall_extensions.pdf)。以下原有推导属于基线成果；新扩展的范围另列于文末。两份完整证明分别保留，未以扩展替换旧稿。

本文给出 Katthän 的 Lecture Hall 序列与带符号 Stieltjes–Rogers 多项式之间的明确对应，由此证明：按原论文例子及文字描述共同确定的定义，所有下标的 Lecture Hall 序列项均为整系数多项式。这正是 arXiv:1809.01377v1 的 Conjecture 3.4。

## 命题与明确公式

对序列 \(P\)，令
\[
M(P)_{r,c}=
\begin{cases}
-P_{c-r+1},&c\ge r,\\
0,&c<r,
\end{cases}
\qquad
E_i(P)=-
\det M(P)_{\{1,\ldots,\lceil i/2\rceil\},
\{\lfloor i/2\rfloor+1,\ldots,i\}}.
\]
Lecture Hall 序列 \(\ell_1,\ell_2,\ldots\) 由方程
\[
E_i(\ell)=\prod_{j=1}^{i}y_j^{\,i+1-j}\qquad(i\ge1)
\]
唯一确定。

定义
\[
\alpha_h=\varepsilon_h y_hy_{h+1},\qquad
\varepsilon_h=
\begin{cases}
-1,&h\ge4\text{ 且 }h\text{ 为偶数},\\
1,&\text{其余情形}.
\end{cases}
\]
令 \(\mu_n\) 为长度 \(2n\) 的所有 Dyck 路径的权重和：路径从高度 \(0\) 出发并返回高度 \(0\)，不经过负高度，每个上步权重为 \(1\)，从高度 \(h\) 下降的下步权重为 \(\alpha_h\)。则
\[
\boxed{\ell_{n+1}=y_1\mu_n\quad(n\ge0).}
\]

有限长度路径只有有限条，所用高度不超过 \(n\)，因而
\[
\ell_i\in\mathbb Z[y_1,\ldots,y_i]\qquad(i\ge1).
\]
这里的多项式性不要求系数非负。

## 为什么该公式满足原定义

证明将原 Toeplitz 方形子矩阵反转行序，分别得到无移位及一次移位的 Hankel 行列式。通用 Stieltjes–Rogers 恒等式给出
\[
\det[\mu_{r+s}]_{0\le r,s<m}
=\prod_{h=1}^{m-1}(\alpha_{2h-1}\alpha_{2h})^{m-h},
\]
\[
\det[\mu_{r+s+1}]_{0\le r,s<m}
=\alpha_1^m\prod_{h=1}^{m-1}(\alpha_{2h}\alpha_{2h+1})^{m-h}.
\]

代入上述带符号权重，并计入反转行序、提出负号以及每项中的 \(y_1\)，便得到每一个定义方程 \(E_i(\ell)=\prod_j y_j^{i+1-j}\)。定义方程对当前未知项线性，其系数是非零单项式；因此有理函数解唯一，路径公式确实给出原序列。这个论证覆盖任意下标，不依赖有限计算外推。

## 原文两处排印问题

[原论文第 3 页](https://arxiv.org/pdf/1809.01377v1)将列集合起点印为 \(\lfloor i/2\rfloor\)，与规定的 \(\lceil i/2\rceil\) 行相比多一列。这里采用 \(\lfloor i/2\rfloor+1\)：它符合该段关于“右上角为 \(-P_i\)、顶端对齐、不含三角零元的最大方阵”的描述，也符合 Example 3.2 的四个行列式及 Definition 4.1 的列平移约定。

第 4 页 Example 3.2 给出的 \(\ell_4\) 最后一个单项式也与该例自己的定义方程不符。由方程直接求得
\[
\ell_4=y_1^2y_2^3(y_1+y_3)^2+y_1^2y_2^2y_3^2y_4,
\]
与同文 Section 6 的列表以及 Example 4.5 的展开一致。本文依据这些相互印证的定义和计算解释排印问题。

## 与既有工作的关系和结果范围

加权路径与形式连分式的对应属于 Flajolet 的经典理论。Sokal 的已发表论文中，Theorem 9.1(b) 给出所用的 Dyck 路径解释，Theorem 9.5(b,c) 给出两个通用 Hankel 分解。本文使用这些已知工具；具体内容是带符号参数识别、Toeplitz 到 Hankel 的转换，以及用定义方程与唯一性确认其适用于 Katthän 的序列。[文献及其作用](REFERENCES.md)

这些通用定理经本文给出的桥梁可以推出目标，并不意味着既有论文已经明确记载了这一特定应用。本材料不作确定的优先权主张。

基线论文的范围是 Conjecture 3.4 的全下标多项式性，以及原稿中的 composition 系数公式和 `i>=2` 时恰有 `2^(i-2)` 个非零单项式的结论。基线本身没有证明 Conjecture 4.2；本版新增扩展另行给出该结论的完整证明。

## 本版扩展

对每个 `n>=1`、每个域，在独立变量和指定 degree-lex 顺序下，初始代数等于 Lecture Hall 半群代数，`2^(n-1)` 个指定顶行 minors 构成 monic 最小 SAGBI 基。扩展同时给出原 Problem 5.1 指定首项映射的公式及逆、generic Schur–Dyck 首项递推，以及整数上显式自由平坦族。自由模基为无限秩，不能误写成有限秩。

原题方阵列索引、第四多项式及 Examples 4.4–4.5 的符号解释均需按定义及相互印证的矩阵读取，不冒称作者正式勘误。结果不声称任意数值特化仍保留代数独立性或 SAGBI 基，也不解决除数为零时完整定义系统的唯一性。

本版没有重跑两个完整计算套件。扩展存档的第二次再生成曾超时，随后分段补算；不能写成两次完整单进程通过。完整复现的独立环境、数据格式和命令见 README。经典生成函数、Hankel/Jacobi–Trudi 工具及基线多项式性不作为本轮新发现；不声称全球首创或人类同行评审；这些扩展结论尚未进行 Lean 形式化。

## 证明与计算材料

英文证明见 main.pdf，可编辑源文件为 main.tex。verify.py 提供精确的有限检查，具体范围见脚本与 verification.json；这些检查用于复核公式，完整证明承担全下标结论。依赖及运行、编译命令见 [README](README.md)。

本研究在 AI 辅助下完成。

