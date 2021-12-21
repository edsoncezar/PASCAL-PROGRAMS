unit AG;

{
-------------------------------------------------------------------------------
Código de Algoritmo Genético

Desenvolvido em 1999 para o Depto. de Ciência da Computação da Universidade
Federal de Juiz de Fora

Orientador: Hélio J. C. Barbosa
Desenvolvedor: André da Motta Salles Barreto
Dúvidas, críticas e/ou sugestões: amsb@acessa.com
-------------------------------------------------------------------------------
Você pode utilizar esse código livremente, desde que sejam mantidos os créditos
originais.
}


interface

uses aleatorios, sysutils, math;


const
   maxPop = 100; // Tamanho máximo da população
   maxCrom = 31; // Tamanho máximo do cromossomo


type
    { Tipos que definem conjuntos limitados de inteiros }
    tLimiteCrom = 0..maxCrom;
    tVetorLimiteCrom = array[1..maxCrom] of tLimiteCrom;
    tLimitePop = 0..maxPop;
    tVetorLimitePop = array[1..maxPop] of tLimitePop;


    { Tipos que definem conjuntos limitados de valores não inteiros }
    tAjuste= (Esquerda, Direita, Centro);
    tTipoSelecao = (roleta, rank);
    tTipoOtimizacao  = (maximizacao, minimizacao);


    { Tipos que definem as estruturas usadas no AG}
    tAlelo = boolean;
    tCromossomo = array [1..maxCrom] of tAlelo;
    tIndividuo = record
               cromossomo:tCromossomo;
               aptidao:real;
               pai,mae:tLimitePop;
               pontoCorte:tVetorLimiteCrom;
               mutacao:tLimiteCrom;
               elitismo: boolean;
               end;
    tPopulacao = record
               individuos: array[1..maxpop] of tIndividuo;
               somaAptidoes, maiorAptidao, menorAptidao, mediaAptidoes:real;
               melhoresIndividuo:tVetorLimitePop;
               melhorIndividuo, piorIndividuo: tLimitePop;
               end;

    { Cabeçalho dos procedimentos }
    procedure inicializa(var populacao:tPopulacao);
    function seleciona(var populacao:tPopulacao; tipoSelecao: tTipoSelecao):tLimitePop;
    procedure crossover(var pai, mae, filho1, filho2:tIndividuo);
    function mutacao(var individuo:tIndividuo):boolean;
    procedure geracao(var popAntiga,popNova:tPopulacao);
    function avalia(cromossomo:tCromossomo):real;
    procedure quickSort(var populacao:tPopulacao; limiteInferior, limiteSuperior: tlimitePop);
    function binarioParaInteiro(cromossomo:tCromossomo; inicioCrom, fimCrom: integer):longInt;//maxCrom=31
    function binarioParaReal(cromossomo:tCromossomo; inicioCrom, fimCrom,
      limiteInferior, limiteSuperior: integer):real;
    procedure estatisticas(var populacao:tPopulacao);
    procedure relatorio(populacao:tPopulacao);
    procedure Informacoes;
    function inicializaVariaveis(var populacao: tPopulacao; taxaCrossover,taxaMutacao,
    semente:real; tamPopulacao,tamCromossomo, numPontosCrossover,
    numIndividuosElitismo:integer; tipoDeOtimizacao: tTipoOtimizacao; tipoDeSelecao: tTipoSelecao;
    NomeDoArquivo:string):boolean;
    procedure finalizarAG;


var
   probCrossover, probMutacao: real;
   { Probabilidade de ocorrência de crossover e mutação }

   tamPop,numElitismo: tLimitePop;
   { Tamanho da população e número de indivíduos mantidos no elitismo}

   tamCrom , numPtsCross:tLimiteCrom;
   { Tamanho do cromossomo e número de pontos do crossover (0 = uniforme) }

   tipoOtimizacao: tTipoOtimizacao;
   { Tipo do problema a ser resolvido: maximização ou minimização }

   tipoSelecao: tTipoSelecao;
   { Tipo de seleção }

   Arquivo:TextFile;
   { Arquivo de saída }


implementation


function avalia(cromossomo:tCromossomo):real;
{ Avalia a aptidão de um indivíduo- ESSA FUNÇÃO DEVE SER ALTERADA DE ACORDO
COM O PROBLEMA A SER RESOLVIDO }
var
i:integer;
x1,x2,soma:real;
begin
soma:=0;
for i:=1 to tamCrom do
    if cromossomo[i] then soma:=soma+1;
avalia:=soma;
{x1:=binarioParaInteiro(cromossomo,1,15);
x2:=binarioParaInteiro(cromossomo,16,30);
avalia:=abs(pi - x1/(x2+1));}
end;

procedure inicializa(var populacao:tPopulacao);
{Inicializa aleatoriamente uma população de indivíduos binários}
var
i,j:integer;
begin
for i:=1 to tamPop do
    begin
    for j:=1 to tamCrom do
        begin
        populacao.individuos[i].cromossomo[j]:=caraCoroa(0.5);
        populacao.individuos[i].pontoCorte[j]:=0;
        end;
    populacao.individuos[i].pai:=0;
    populacao.individuos[i].mae:=0;
    populacao.individuos[i].aptidao:=avalia(populacao.individuos[i].cromossomo);
    populacao.individuos[i].mutacao:=0;
    populacao.individuos[i].elitismo:=false;
    end;
estatisticas(populacao);
end;


function seleciona(var populacao:tPopulacao; tipoSelecao: tTipoSelecao):tLimitePop;
{ Seleciona um indivíduo pelo método especificado }
var
rand, somaParcial:real;
indPop:integer;
begin
indPop:=0;
case tipoSelecao of
     roleta:
            begin
            somaParcial:=0;
            rand:=aleatorio * populacao.somaAptidoes;
            repeat
               inc(indPop);
               somaParcial:=somaParcial+populacao.individuos[indPop].aptidao;
               until (somaParcial>=rand) or (indPop=tamPop);
            seleciona:=indPop;
            end;
     rank:
          begin
          indPop:=trunc (tamPop * (1.5 - sqrt (2.25 - 2 * aleatorio())));
          if (indPop < 1) then  indPop := 1;
          seleciona:= indPop;
          end;
     else seleciona:=0;
     end;
end;


procedure crossover(var pai, mae, filho1, filho2:tIndividuo);
{ Crossover de n pontos para indivíduos binários (n = numPtsCross) }
var
i,cont,pontoAnterior:integer;
podeContinuar:boolean;
pontoCorte: tVetorLimiteCrom;
begin
// Inicialização das variáveis

for i:=1 to numPtsCross do pontoCorte[i]:=0;

//Crossover uniforme
if NumPtsCross = 0 then
   begin
   for i:=1 to tamCrom do
       if caraCoroa(0.5) then
          begin
          pontoCorte[i]:=1; // O vetor de pontos de corte passa a guardar a máscara
          filho1.cromossomo[i]:=pai.cromossomo[i];
          filho2.cromossomo[i]:=mae.cromossomo[i];
          end
       else
           begin
           pontoCorte[i]:=0;
           filho1.cromossomo[i]:=mae.cromossomo[i];
           filho2.cromossomo[i]:=pai.cromossomo[i];
           end;
   end
else
    begin
    podeContinuar:=true;
    if numPtsCross > tamCrom-1 then numPtsCross :=tamCrom-1;
    { Isso porque um crossover com o número de pontos igual ao tamanho do cromossomo
    tem efeito máximo equivalente a se ele tivesse como número de pontos o
    tamanho do cromossomo menos 1 }

    if caraCoroa(probCrossover) then pontoCorte[1]:=alt(1,tamCrom)
    else
        begin
        podeContinuar:=false; //Não ocorre crossover
        filho1:=pai;
        filho2:=mae;
        end;

    if podeContinuar then // Crossover de numPtsCross pontos
       begin
       cont:=0;
       pontoAnterior:=0;
       repeat
           inc(cont);
           if (cont mod 2 =1) then
              begin
              for i:=pontoAnterior+1 to pontoCorte[cont] do
                  begin
                  filho1.cromossomo[i]:=pai.cromossomo[i];
                  filho2.cromossomo[i]:=mae.cromossomo[i];
                  end;
              end
           else
               begin
               for i:=pontoAnterior+1 to pontoCorte[cont] do
                   begin
                   filho1.cromossomo[i]:=mae.cromossomo[i];
                   filho2.cromossomo[i]:=pai.cromossomo[i];
                   end;
               end;
           pontoAnterior:=pontoCorte[cont];
           if caraCoroa(probCrossover) then pontoCorte[cont+1]:=alt(pontoCorte[cont]+1,tamCrom)
           else pontoCorte[cont+1]:=tamCrom;
           until (cont = numPtsCross) or (pontoCorte[cont] = tamCrom);

       if (cont mod 2 =0) then
          begin
          for i:=(pontoCorte[cont]+1) to tamCrom do
              begin
              filho1.cromossomo[i]:=pai.cromossomo[i];
              filho2.cromossomo[i]:=mae.cromossomo[i];
              end;
          end
       else
           begin
           for i:=(pontoCorte[cont]+1) to tamCrom do
               begin
               filho2.cromossomo[i]:=pai.cromossomo[i];
               filho1.cromossomo[i]:=mae.cromossomo[i];
               end;
           end;

       if (cont+1 <= numPtsCross) and (pontoCorte[cont] = tamCrom) then
          for i:=cont+1 to numPtsCross do pontoCorte[i]:=0;
       end;
    end;

filho1.pontoCorte:=pontoCorte;
filho2.pontoCorte:=pontoCorte;

mutacao(filho1);
mutacao(filho2);
end;


function mutacao(var individuo:tIndividuo):boolean;
{ Aplica o operador de mutação a um indivíduo }
var
sorteado: integer;
begin
if caraCoroa(probMutacao) then
   begin
   sorteado:=alt(1,tamCrom);
   individuo.cromossomo[sorteado]:=not(individuo.cromossomo[sorteado]);
   individuo.mutacao:=sorteado;
   mutacao:=true;
   end
else mutacao:=false;
end;

procedure geracao(var popAntiga,popNova:tPopulacao);
{ Gera uma nova população, utilizando os operadores genéticos }
var
i,j,pai, mae: tLimitePop;
begin

for i:=1 to numElitismo do
    begin
    popNova.individuos[i]:=popAntiga.individuos[i];
    popNova.individuos[i].pai:=i;
    popNova.individuos[i].mae:=0;
    for j:=1 to tamCrom do popNova.individuos[i].pontoCorte[j]:=0;
    popNova.individuos[i].mutacao:=0;
    popNova.individuos[i].elitismo:=true;
    end;

i:=numElitismo+1;

while (i<=tamPop-1) do
      begin
      pai:=seleciona(popAntiga, tipoSelecao);
      mae:=seleciona(popAntiga, tipoSelecao);
      crossover(popAntiga.individuos[pai],popAntiga.individuos[mae],
               popNova.individuos[i],popNova.individuos[i+1]);

      popNova.individuos[i].aptidao:=avalia(popNova.individuos[i].cromossomo);
      popNova.individuos[i].pai:=pai;
      popNova.individuos[i].mae:=mae;
      popNova.individuos[i].elitismo:=false;

      popNova.individuos[i+1].aptidao:=avalia(popNova.individuos[i+1].cromossomo);
      popNova.individuos[i+1].pai:=pai;
      popNova.individuos[i+1].mae:=mae;
      popNova.individuos[i+1].elitismo:=false;

      i:=i+2;
      end;

if i=tamPop then //ficou faltando um indivíduo
   begin
   j:=seleciona(popAntiga, tipoSelecao);
   popNova.individuos[i]:=popAntiga.individuos[j];
   popNova.individuos[i].pai:=j;
   popNova.individuos[i].mae:=0;
   for j:=1 to tamCrom do popNova.individuos[i].pontoCorte[j]:=0;
   popNova.individuos[i].mutacao:=0;
   popNova.individuos[i].elitismo:=true;
   end;

quickSort(popNova,1,tamPop);
estatisticas(popNova);
end;


procedure quickSort(var populacao:tPopulacao; limiteInferior,limiteSuperior:tLimitePop);
{ Procedimento de ordenação utilizando o método QuickSort}
var
esq,dir:tLimitePop;
pivo,aux:tIndividuo;
begin
esq:=limiteInferior;
dir:=limiteSuperior;
pivo:=populacao.individuos[(limiteInferior+limiteSuperior) div 2];

while(esq <= dir) do
   begin
   if tipoOtimizacao=maximizacao then
      begin
      while (populacao.individuos[esq].aptidao > pivo.aptidao) do inc(esq);
      while (populacao.individuos[dir].aptidao < pivo.aptidao) do dec(dir);
      end
   else
       begin
       while (populacao.individuos[esq].aptidao < pivo.aptidao) do inc(esq);
       while (populacao.individuos[dir].aptidao > pivo.aptidao) do dec(dir);
       end;
   if (esq <= dir) then
      begin
      aux:=populacao.individuos[esq];
      populacao.individuos[esq]:=populacao.individuos[dir];
      populacao.individuos[dir]:=aux;
      inc(esq);
      dec(dir);
      end;
    end;

if (dir-limiteInferior)>0 then quickSort(populacao,limiteInferior,dir);
if (limiteSuperior-esq)>0 then quickSort(populacao,esq,limiteSuperior);
end;



function binarioParaInteiro(cromossomo:tCromossomo; inicioCrom, fimCrom: integer):longInt;
{Converte um número binário em um número inteiro}
var
i:integer;
acumulador, potenciaDe2:longInt;
begin
acumulador:=0;
potenciaDe2:=1;
if (tamCrom > maxCrom) or (inicioCrom>fimCrom) then binarioParaInteiro:=-1
else
    begin
    for i:=fimCrom downto inicioCrom do
        begin
        if cromossomo[i] then acumulador:=acumulador+potenciaDe2;
        potenciaDe2:=potenciaDe2*2;
        end;
        binarioParaInteiro:=acumulador;
    end;
end;

function binarioParaReal(cromossomo:tCromossomo; inicioCrom, fimCrom,
limiteInferior, limiteSuperior: integer):real;
{Converte um número binário em um número inteiro}
begin
binarioParaReal:=limiteInferior + binarioParaInteiro(cromossomo, inicioCrom,fimCrom)*
(limiteSuperior - limiteInferior)/ (power(2,(fimCrom-inicioCrom+1))-1);
end;


procedure estatisticas(var populacao:tPopulacao);
{Calcula estatísticas de uma população}
var
i: integer;
begin
populacao.somaAptidoes:=populacao.individuos[1].aptidao;
populacao.menorAptidao:=populacao.individuos[1].aptidao;
populacao.maiorAptidao:=populacao.individuos[1].aptidao;
populacao.melhorIndividuo:=1;
populacao.piorIndividuo:=1;
for i:=2 to tamPop do
    with populacao.individuos[i] do
         begin
         populacao.somaAptidoes:=populacao.somaAptidoes+populacao.individuos[i].aptidao;
         if aptidao > populacao.maiorAptidao then
            begin
            populacao.maiorAptidao:=aptidao;
            populacao.melhorIndividuo:=i;
            end;
         if aptidao < populacao.menorAptidao then
            begin
            populacao.menorAptidao:=aptidao;
            populacao.piorIndividuo:=i;
            end;
         end;
populacao.mediaAptidoes:=populacao.somaAptidoes / tamPop;
end;

function otimizacaoParaString(tipoOtimizacao:tTipoOtimizacao):string;
begin
case tipoOtimizacao of
     maximizacao: otimizacaoParaString:='maximização';
     minimizacao: otimizacaoParaString:='minimização';
     else otimizacaoParaString:='';
     end;
end;

function selecaoParaString(tipoSelecao:tTipoSelecao):string;
begin
case tipoSelecao of
     rank: selecaoParaString:='rank';
     roleta: selecaoParaString:='roleta (proporcional)';
     else selecaoParaString:='';
     end;
end;

function cromossomoParaString(cromossomo:tCromossomo):string;
{Função auxiliar; retorna o cromossomo especificado como
uma string de 0's e 1's}
var
i:integer;
strTemp:string;
begin
strTemp:='';
for i:=1 to tamCrom do
    if cromossomo[i] then strTemp:=strTemp+'1'
    else strTemp:=strTemp+'0';
cromossomoParaString:=strTemp;
end;

function tab(caracter:char;repeticao:integer):string; //melhorar
{função auxiliar; retorna uma string com um conjunto de n caracteres iguais}
var
i:integer;
strTemp:string;
begin
strTemp:='';
for i:=1 to repeticao do strTemp:=strTemp+caracter;
tab:=strTemp;
end;

procedure escreveBloco(texto:string; tamanhoBloco: integer; ajuste: tAjuste);
{procedimento auxiliar; preenche um bloco de tamanho n, com o texto
alinhado da maneira especificada. Facililita a tabulação do relatório}
begin
case ajuste of
     esquerda:
        begin
        write(Arquivo,texto);
        write(Arquivo,tab(' ',tamanhoBloco-length(texto)));
         end;
     direita:
        begin
        write(Arquivo,tab(' ',tamanhoBloco-length(texto)));
        write(Arquivo,texto);
        end;
     centro:
        begin
        write(Arquivo,tab(' ',(tamanhoBloco-length(texto)) div 2));
        write(Arquivo,texto);
        write(Arquivo,tab(' ',(tamanhoBloco-length(texto))-(tamanhoBloco-length(texto)) div 2));
        end;
     end;
end;


procedure Informacoes;
begin
{Apenas imprime no Arquivo um cabeçalho}
writeln(Arquivo, 'Algoritmo Genético');
writeln(Arquivo, tab('-',18));
writeln(Arquivo);
writeln(Arquivo);
writeln(Arquivo, 'Dados:');
writeln(Arquivo, tab('-',50));
writeln(Arquivo,'Tipo de otimização:  '+ otimizacaoParaString(tipoOtimizacao));
writeln(Arquivo,'Tamanho do cromossmo: '+ inttostr(tamCrom));
writeln(Arquivo,'Tamanho da população: '+ inttostr(tamPop));
writeln(Arquivo,'Probabilidade de Crossover: '+floattostr(probCrossover));
writeln(Arquivo,'Probabilidade de Mutação: '+floattostr(probMutacao));
writeln(Arquivo,'Número de pontos do crossover*:  '+inttostr(numPtsCross));
writeln(Arquivo,'Tipo de seleção: '+selecaoParaString(tipoSelecao));
writeln(Arquivo, 'Número de indivíduos mantidos por elitismo: '+inttostr(numElitismo));
writeln(Arquivo, tab('-',50));
writeln(Arquivo,'* 0 ponto = crossover uniforme');
writeln(Arquivo);
writeln(Arquivo);
writeln(Arquivo, 'Legenda:');
writeln(Arquivo, tab('-',50));
writeln(Arquivo, 'Cn: ponto de corte n');
writeln(Arquivo, 'M: ponto de mutação');
writeln(Arquivo, 'E: existiu elitismo');
writeln(Arquivo, tab('-',50));
writeln(Arquivo);
writeln(Arquivo);
end;




procedure relatorio(populacao:tPopulacao);
{Gera um arquivo com um relatório sobre a população especificada}
var
delta,i,j:integer;
cromoTemp:tCromossomo;
begin
// Dá pra generalizar mais, trocando os valores numéricos pelo comprimento
// das constantes (length)

escreveBloco('Ordem',5,esquerda);
escreveBloco('Cromossomo',tamCrom+5,centro);
//escreveBloco('x1',5,direita);
//escreveBloco('x2',5,direita);
escreveBloco('Aptidão',20,direita);
escreveBloco('Pai',5,direita);
escreveBloco('Mãe',5,direita);
if numPtsCross=0 then
   begin
   escreveBloco('Máscara',tamCrom+5,centro);
   delta:=tamCrom+5;
   end
else
    begin
    for i:=1 to numPtsCross do escreveBloco('C'+inttostr(i),5,direita);
    delta:=5*numPtsCross;
    end;
escreveBloco('M',5,direita);
escreveBloco('E',5,centro);
writeln(Arquivo);
writeln(Arquivo, tab('_',55+delta+tamCrom));
writeln(Arquivo);

for i:=1 to tamPop do
    begin
    escreveBloco(inttostr(i),5,esquerda);
    escreveBloco(cromossomoParaString(populacao.individuos[i].cromossomo),tamCrom+5,centro);
   // escreveBloco(inttostr(binarioParaInteiro(populacao.individuos[i].cromossomo,1,15)),5,direita);
  //  escreveBloco(inttostr(binarioParaInteiro(populacao.individuos[i].cromossomo,16,30)),5,direita);
    escreveBloco(floattostr(populacao.individuos[i].aptidao),20,direita);
    escreveBloco(inttostr(populacao.individuos[i].pai),5,direita);
    escreveBloco(inttostr(populacao.individuos[i].mae),5,direita);
    if numPtsCross=0 then
       begin
       for j:=1 to tamCrom do
           if populacao.individuos[i].pontoCorte[j]=1 then cromoTemp[j]:=true
           else cromoTemp[j]:=false;
       escreveBloco(cromossomoParaString(cromoTemp),tamCrom+5,centro);
       end
    else for j:=1 to numPtsCross do escreveBloco(inttostr(populacao.individuos[i].pontoCorte[j]),5,direita);
    escreveBloco(inttostr(populacao.individuos[i].mutacao),5,direita);
    if (populacao.individuos[i].elitismo=true) then escreveBloco('S',5,centro)
    else escreveBloco('N',5,centro);
    writeln(Arquivo);
    end;
writeln(Arquivo,tab('_',55+delta+tamCrom));
writeln(Arquivo, 'Aptidao média da população: '+ floatToStr(populacao.mediaAptidoes));
writeln(Arquivo, 'Maior aptidão da população: '+ floatToStr(populacao.maiorAptidao));
writeln(Arquivo, 'Indivíduo com a maior aptidão: '+ floatToStr(populacao.melhorIndividuo));
writeln(Arquivo, 'Menor aptidão da população: '+ floatToStr(populacao.menorAptidao));
writeln(Arquivo, 'Indivíduo com a menor aptidão: '+ floatToStr(populacao.piorIndividuo));
writeln(Arquivo,'Soma das aptidões: '+ floatToStr(populacao.somaAptidoes));
writeln(Arquivo);
writeln(Arquivo);
end;


function inicializaVariaveis(var populacao: tPopulacao; taxaCrossover,taxaMutacao,
semente:real; tamPopulacao,tamCromossomo, numPontosCrossover,
numIndividuosElitismo:integer; tipoDeOtimizacao: tTipoOtimizacao; tipoDeSelecao: tTipoSelecao;
NomeDoArquivo:string):boolean;
{ Inicializa as variáveis globais; esse procedimento deve ser o primeiro a
ser chamado    }
var
deuCerto:boolean;
tamanhoOriginal,i:integer;

begin
deuCerto:=true;

if (taxaCrossover >= 0) and (taxaCrossover<=1) then probCrossover:=taxaCrossover
else
    begin
    probCrossover:=0;
    deuCerto:=false;
    end;

if (taxaMutacao >= 0) and (taxaMutacao <=1) then probMutacao:=taxaMutacao
else
    begin
    probMutacao:=0;
    deuCerto:=false;
    end;

if not(forneceSemente(semente)) then deuCerto:=false;

if tamPopulacao>0 then tamPop:=tamPopulacao
else
    begin
    tamPop:=0;
    deuCerto:=false;
    end;


if tamCromossomo>0 then tamCrom:=tamCromossomo
else
    begin
    tamCrom:=0;
    deuCerto:=false;
    end;


if (numPontosCrossover >= 0) then numPtsCross:= numPontosCrossover
else
    begin
    numPtsCross:=0;
    deuCerto:=false;
    end;

if (numIndividuosElitismo >= 0) then numElitismo:=numIndividuosElitismo
else
    begin
    numElitismo:=0;
    deuCerto:=false;
    end;

case tipoDeOtimizacao of
     maximizacao: tipoOtimizacao:=maximizacao;
     minimizacao:tipoOtimizacao:=minimizacao;
     else tipoOtimizacao:=maximizacao; //default
     end;

case tipoDeSelecao of
     rank: tipoSelecao:=rank;
     roleta: begin
             if tipoOtimizacao=maximizacao then tipoSelecao:=roleta
             else tipoSelecao:=rank;
             end;
     else tipoSelecao:=rank;
     end;

if (nomeDoArquivo<>'') then
   begin
   i:=0;
   tamanhoOriginal:=length(nomeDoArquivo);
   nomeDoArquivo:=nomeDoArquivo+'.ag';
   repeat
      inc(i);
      if FileExists(nomeDoArquivo) then nomeDoArquivo:=copy(nomeDoArquivo,1,tamanhoOriginal)+inttostr(i)+'.ag'
      else i:=-1;
      until i=-1;
   try
      AssignFile(Arquivo,nomeDoArquivo);
   except
         deuCerto:=false;
   end;

   try
      rewrite(Arquivo);
   except
         deuCerto:=false;
   end;
   end;

if deuCerto then inicializa(populacao);
quickSort(populacao,1,tamPop);
inicializaVariaveis:=deuCerto;
end;

procedure finalizarAG;
{Faz as finalizações necessárias}
begin
closeFile(Arquivo);
end;

end.
