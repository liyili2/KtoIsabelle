procedure main()
{
var i : int;
var m : int;
var n : int;
var q : int;
var r : int;
var s : int;
var t : int;
var x : int;
var y : int;
var z : int;
m := 10;
n := 2;
while (n <= m)
{
i := 2;
q := n div i;
t := 1;
while (i<=q && 1<=t)
{
x := i;
y := q;
z := 0;
while (!(x <= 0))
{
q := x div 2;
r := q+q+1;
if (r <= x)
{
z := z+y;
}
else
{
}
x := q;
y := y+y;
}
if (n <= z)
{
t := 0;
}
else
{
i := i+1;
q := n div i;
}
}
if (1 <= t)
{
s := s+1;
}
else
{
}
n := n+1;
}
}
