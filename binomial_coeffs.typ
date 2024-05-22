#import "cfg.typ": cfg
#show: cfg

= Биноминальные коэффициенты
$binom(abs(X), i) := abs({y subset.eq X | |y| = i})$.

$binom(n, i) = n!/(i! (n - i)!)$.

$binom(n, i) = binom(n, n - i)$.

$binom(n + 1, i + 1) = binom(n, i) + binom(n, i + 1)$.

$(a + b)^n = sum_(i = 0)^n binom(n, i) a^i b^(n - i)$.

$sum_(i = 0)^n binom(n, i) = 2^n$.

Тождество Вандермонда: $sum_(i = 0)^n binom(p, i) binom(q, n - i) = binom(p + q, n)$.

$0 <= l + k <= n ->
sum_(i = k)^(n - l) binom(i, k) binom(n - i, l) = binom(n + 1, k + l + 1)$.
