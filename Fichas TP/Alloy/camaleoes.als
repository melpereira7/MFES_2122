/* 
Complete o seguinte modelo de uma colónia de camaleões onde o número de 
camaleões é fixo mas onde a cor de cada camaleão pode mudar de acordo com
as seguintes regras: 
- As cores possíveis são Verde, Azul e Amarelo
- Se 2 camaleões de cores diferentes se encontram mudam ambos para a terceira cor
- As cores só se alteram na situação acima 
*/

abstract sig Cor{}
one sig Verde, Azul, Amarelo extends Cor{}

sig Camaleao {
	var cor: one Cor
}

fact init {
	some Camaleao
	all c: Camaleao | some c.cor
}


pred nop {
	cor' = cor
}

pred encontro[x,y : Camaleao] {
	//guards

	x in Camaleao and y in Camaleao and x!=y
	
	//effects

	x.cor != y.cor	implies x.cor' = Cor-x.cor-y.cor and y.cor' = Cor-x.cor-y.cor
				else x.cor' = x.cor and y.cor' = y.cor

	//frame conditions
	
	all c: Camaleao-x-y | c.cor' = c.cor
}

fact Comportamento {
	always (nop or some x,y : Camaleao | encontro[x,y])
}

// Especifique as seguintes propriedades desta colónia

assert Estabilidade {
	// Se os camaleoes ficarem todos da mesma cor, as cores nunca mais mudam
	always one Camaleao.cor&Cor implies always Camaleao.cor' = Camaleao.cor
}

check Estabilidade for 5

assert NaoConvergencia {
	// Se inicialmente há um camaleao verde e nenhum azul então não é possível
	// que a colónia fique toda amarela
	one Camaleao.cor&Verde and no Camaleao.cor&Azul implies Camaleao.cor!=Amarelo
}

check NaoConvergencia for 5

// Especifique um cenário onde existe um camaleao que não para de mudar de cor
// tomando recorrentemente todas as cores possíveis

run Exemplo {
	one c: Camaleao | c.cor = Amarelo and (Camaleao-c).cor = Verde
} for exactly 3 Camaleao

