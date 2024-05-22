#import "cfg.typ": cfg
#show: cfg

= Шкала Крипке
Шкала Крипке $:=$ ограниченный ЧУМ по включению, элементами которого являются множества
переменных. Мир $:=$ элемент. $w forces x := $ $x$ истинна в мире $w := x in w$.

Индуктивное определение истинности формулы:
- $w forces A -> w forces B -> w forces A and B$.

- $cases(delim: "[", w forces A, w forces B) -> w forces A or B$.

- $(forall s >= w space s forces A -> s forces B) -> w forces A => B$.

- $(forall s >= w space s forces.not A) -> w forces not A$.

$s >= w -> w forces A -> s forces A$.

Корректность интуиционистского ИВ относительно шкал Крипке: $tack.r A -> w forces A$.

Полнота интуиционистского ИВ относительно шкал Крипке: $tack.r.not A -> exists w
forces.not A$.
