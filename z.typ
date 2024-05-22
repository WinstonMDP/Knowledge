#import "cfg.typ": cfg
#show: cfg

= $ZZ$
$s$ - делитель $n := n$ - кратное $s := s divides n := n = t s, t in ZZ$.

$n, m$ - ассоциированные $:= n = plus.minus m$.

$n divides m -> m divides n -> n = plus.minus m$.

$p$ простое $:= exists.not p' != plus.minus 1, plus.minus p space p' divides p$.

Основная теорема арифметики:
$forall n in QQ space
n > 0 -> exists! $ разложение $n = p_1^(epsilon_1) p_2^(epsilon_2) ...$

Теорема Евклида: ${x in ZZ | x "простое"}$ бесконечно.

$n = plus.minus p_1^alpha_1... ->
m = plus.minus p_1^beta_1... ->
"НОД"(n, m) := p_1^min(alpha_1, beta_1)...$

$"НОД"(n, m) divides n$.

$d divides n -> d divides m -> d divides "НОД"(n, m)$.

$n divides "НОК"(n, m)$.

$n divides u -> m divides u -> "НОК"(n, m) divides u$.

$"НОД"(n, m) "НОК"(n, m) = n m$.

$n, m$ - взаимно простые $:= "НОД"(n, m) = 1$.

$forall b != 0 space exists q, r in ZZ space cases(0 <= r < |b|, a = b q + r)$.

$"НОД"(n, m) = min{n u + m v | exists u, v in ZZ space n u + m v > 0}$.

Функция Эйлера $:= op(phi) n = abs({x in NN med mid(|) med cases(x < n, "НОД"(x, n) = 1)})$.
