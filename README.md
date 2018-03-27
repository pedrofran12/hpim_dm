# pim

How to perform tests:

`spin -a -f "!(<>([]test))" reliable.pml`

`gcc -O2 -o pan pan.c -DBITSTATE` <- corresponde a uma aproximacao no entanto é a unica maneira rapida de fazer testes (por enquanto)

`./pan`




Teste:
3 nós
 - 1 downstream (modo interest)
 - 2 upstream (ambos iniciam em estado AW)

Suposto o AW (router com menor metrica) ter conhecimento de todos os routers e permanecer como AW
O router AL (router com maior metrica) deverá transitar de AW->AL


Mensagens:
Estao a ser enviadas de forma reliable (não existem perdas), no entanto um non-AW continua a enviar msgs (para todos), acerca do seu estado, enquanto o AW não responder (QuACK) contendo o estado mais recente do router
