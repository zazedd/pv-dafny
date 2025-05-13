// forall n, sum(n, i = 1, i * i!) = (n + 1)! - 1

function fact (n : nat) : nat
  decreases n
{
  if (n == 0) then 1
  else if (n == 1) then 1
  else n * fact (n - 1)
}

function sum (i : nat) : nat
  decreases i
{
  if (i == 0) then 0
  else i * fact(i) + sum(i - 1)
}

lemma {:induction false} one (n : nat)
  ensures sum(n) == fact(n + 1) - 1
  decreases n
{
  if n == 0 { } else {
    one(n - 1);
  }
}
