let halt = x => console.log(x)

function f (x, k1) {
	k1(x) /*1*/
}
function g (y, k2) {
	k2(y) /*2*/
}

let k5 = x4 => {
	x4(g, halt) /*5*/
}
f(f, k5) /*6*/