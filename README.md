# pim

How to perform tests:

`spin -a -f "!(<>([]test))" reliable.pml` or `spin -a -f "!([](<>((global_entries[1].state[1]==al) && (global_entries[2].state[2]==aw) && (global_entries[2].state[1]==al) && (global_entries[2].state[0]==nointerest))))" reliable.pml`

`gcc -O2 -o pan pan.c -DCOLLAPSE`

`./pan -a -f`




Teste:
3 nós
 - 1 downstream (modo nointerest)
 - 2 upstream (ambos iniciam em estado AW)

Suposto o AW (router com menor metrica) ter conhecimento de todos os routers e permanecer como AW
O router AL (router com maior metrica) deverá transitar de AW->AL


Mensagens:
Estao a ser enviadas de forma reliable (não existem perdas), no entanto um non-AW continua a enviar msgs (para todos), acerca do seu estado, enquanto o AW não responder (QuACK) contendo o estado mais recente do router
