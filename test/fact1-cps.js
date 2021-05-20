let halt = x => console.log(x)

function fact (n, k1) {
	let u3 = n <= 1.0
	if (u3) {
		k1(1.0) /*2*/
	}
	else {
		let k6 = x4 => {
			let u7 = n * x4
			k1(u7) /*4*/
		}
		let u8 = n - 1.0
		fact(u8, k6) /*5*/
	}
}

let k11 = x9 => {
	let x = x9
	fact(x, halt) /*9*/
}
fact(3.0, k11) /*10*/
