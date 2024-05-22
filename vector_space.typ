#import "cfg.typ": cfg
#show: cfg

= Векторное пространство
$(V, +, *)$ - векторное пространство над полем F:
- $(V, +)$ - абелева группа
- умножение на скаляр замкнуто
- $lambda(a + b) = lambda a + lambda b$
- $(lambda + mu)a = lambda a + mu a$
- $(lambda mu)a = lambda (mu a)$
- $1a = a$
где $a, b in V, lambda, mu in F$.

Элементы соответствующего поля иногда называют числами, даже когда поле не является
числовым.

Пространство геометрических векторов евклидовой плоскости обозначается через $E^2$.
Это векторное пространство над полем $RR$.

$b = lambda_1 a_1 + ... + lambda_n a_n$ - линейная комбинация векторов $a_1, ..., a_n$.
Вектор $b$ линейно выражается через векторы $a_1, ..., a_n$.

${e_1, e_2, ..., e_n} subset.eq V$ называется базисом векторного пространства $V <->$
каждый вектор $v in V$ единственным образом линейно выражается через $e_1, ..., e_n$.
Коэффициенты этого выражения называются координатами вектора $v$ в базисе ${e_1, e_2,
..., e_n}$.

Всякое векторное пространство $V$ над полем $F$, имеющее базис из $n$ векторов,
изоморфно просранству $K^n$.
