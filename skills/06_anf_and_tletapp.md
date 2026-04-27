# Skill: ANF 编码 — tletapp 只接受 value，不接受 tm

## 问题

`tletapp` 的类型签名是：

```coq
tletapp : value → value → tm → tm
```

它要求前两个参数（函数和参数）都是 `value`，不是 `tm`。
所以如果你有一个 `e : tm`（比如函数的 denotation），
**不能**直接写：

```coq
tletapp e (vfvar x) (tret (vbvar 0))   (* ❌ e : tm，不是 value *)
```

## 解决方案：用 tlete 先 let-bind

ANF（Administrative Normal Form）的标准做法：先把 `e` 的结果 bind 到 `bvar 0`，
再用 `bvar 0` 作为 `tletapp` 的函数：

```coq
tlete e (tletapp (vbvar 0) (vfvar x) (tret (vbvar 0)))
```

语义：`let f = e in f x`，其中 `vbvar 0` 指代 `tlete` 绑定的变量 `f`。

## 在 Denotation 里的体现

类型 `x:τx →, τ` 的 denotation 中，对 `e` 应用 `x`：

```coq
| CTArrow x τx τ =>
    FImpl
      (denot_ty τx (tret (vfvar x)))
      (denot_ty τ (tlete e (tletapp (vbvar 0) (vfvar x) (tret (vbvar 0)))))
      (*              ↑ let-bind e first, then apply bvar 0 to x *)
```

## 规律

凡是需要"对一个 `tm` 类型的表达式做函数应用"，
一律用 `tlete e (tletapp (vbvar 0) arg cont)` 的模式。
