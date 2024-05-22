#import "cfg.typ": cfg
#show: cfg

= Кардиналы
$x lt.tilde y := exists z$ - инъекця из $x$ в $y$.

$x$ равномощно $y := x tilde y := exists z$ - биекция между $x$ и $y$.

$|x| :=$ кардинальное число $x$.

$|x| = |y| := x tilde y$.

Теорема Кантора-Бернштейна-Шрёдера: $cases(x lt.tilde y, y lt.tilde x) <-> x tilde y$.

$|{0, ..., n - 1}| := n$.

$aleph_0 := |NN|$.

$x$ конечное $:= exists n = |x|$.

$x$ бесконечное $:= x$ не конечное.

$x$ конечное $-> y subset.eq x -> |x| = |y| -> x = y$.

$|x| <= |y| <-> exists z subset.eq y space |x| = |z|$.

$x$ бесконечное $<-> aleph_0 <= |x|$.

$x$ бесконечное $<-> exists y subset x space |x| = |y|$.

Теорема Кантора: $|x| < |op(cal(P)) x|$.

$|op(cal(P)) NN| = |RR|$.
