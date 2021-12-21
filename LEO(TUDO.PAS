{program x;

begin
port[$378]:=0;
end.}




Program eixos;

Uses Crt;

Var


  bit1, bit2, bit3, bit4, bit5, bit6, bit7, bit8:byte;

  {eixo A}

  sentidoA:char;
  i, tempoint:integer;
  mm,pulsoi,tempoi,k,z,resultadozero,idivid20:real;
  pulsos,voltasmin,tempo,RPMa,rpm:real;

  {eixo B}

 { sentidoB:char;
  iB, tempointB:integer;
  mmB,pulsoiB,tempoiB,kB,zB,resultadozeroB,idivid20B:real;
  pulsosB,voltasminB,tempoB,RPMaB,rpmB:real;

  {eixo C}

  {sentidoC:char;
  iC, tempointC:integer;
  mmC,pulsoiC,tempoiC,kC,zC,resultadozeroC,idivid20C:real;
  pulsosC,voltasminC,tempoC,RPMaC,rpmC:real;

  {eixo D}

  {sentidoD:char;
  iD, tempointD:integer;
  mmD,pulsoiD,tempoiD,kD,zD,resultadozeroD,idivid20D:real;
  pulsosD,voltasminD,tempoD,RPMaD,rpmD:real;}




e,ee:array[1..100] of real;
f,ff:array[1..100] of real;
g,gg:array[1..100] of real;
h,hh:array[1..100] of real;


a,b:integer;
ch:char;

Const

  data=$378;

Begin

a:=0;
b:=0;

textcolor(14);
Clrscr;

Repeat

 Clrscr;

 a:=a+1;
 b:=b+1;



 {1§ eixo A}

 begin

  clrscr;
  writeln('');writeln('');writeln('');writeln('');

  write('Entre com o valor da coordenada A ==========================>');
  readln(e[a]);

  write('Qual a rota‡Æo do motor em RPM (RPM max = 900 ==============>');
  readln(RPMa);

  RPM :=RPMa*3.2;



 end;
 {2§ eixo B}

{ begin

  clrscr;
  writeln('');writeln('');writeln('');writeln('');

  write('Entre com o valor da coordenada B ==========================>');
  readln(f[a]);

  write('Qual a rota‡Æo do motor em RPM (RPM max = 900 ==============>');
  readln(RPMab);

  RPMb :=RPMab*3.2;



 end;

 {3§ eixo C}

 {begin

  clrscr;
  writeln('');writeln('');writeln('');writeln('');

  write('Entre com o valor da coordenada C ==========================>');
  readln(g[a]);

  write('Qual a rota‡Æo do motor em RPM (RPM max = 900 ==============>');
  readln(RPMac);

  RPMc :=RPMac*3.2;



 end;

 {4§ eixo D}

{ begin

  clrscr;
  writeln('');writeln('');writeln('');writeln('');

  write('Entre com o valor da coordenada D ==========================>');
  readln(h[a]);

  write('Qual a rota‡Æo do motor em RPM (RPM max = 900 ==============>');
  readln(RPMad);

  RPMd :=RPMad*3.2;



 end;}


  writeln;
  write('  Deseja digitar mais algum numero (S/N)        ');

 readln(ch);


until (ch='n') or (ch='N');


Clrscr;

A := 0;

for a:=1 to b do

begin


  gotoxy(14,2);
  writeln('      Os resultados seguem abaixo');
  writeln;
  writeln;

write('          ===========A=========B=========C=========D===========');



  gotoxy(20,5+a);
  writeln('', e[a]:3:2);


              ee[a] := e[a]-e[a-1];


              if (ee[a]>0) and (a>1) then
              begin
              gotoxy(25,5+a);
              writeln('SH');
              end;

              if (ee[a]=0) and (a>1) then
              begin
              gotoxy(25,5+a);
              writeln('MP');
              end;

              if (ee[a]<0) and (a>1) then
              begin
              gotoxy(25,5+a);
              writeln('AH');
              end;


  {gotoxy(30,5+a);
  writeln('', f[a]:3:2);


              ff[a] := f[a]-f[a-1];

              if (ff[a]>0) and (a>1) then
              begin
              gotoxy(35,5+a);
              writeln('SH');
              end;

              if (ff[a]=0) and (a>1) then
              begin
              gotoxy(35,5+a);
              writeln('MP');
              end;

              if (ff[a]<0) and (a>1) then
              begin
              gotoxy(35,5+a);
              writeln('AH');
              end;


  gotoxy(40,5+a);
  writeln('', g[a]:3:2);


              gg[a] := g[a]-g[a-1];

              if (gg[a]>0) and (a>1) then
              begin
              gotoxy(45,5+a);
              writeln('SH');
              end;

              if (gg[a]=0) and (a>1) then
              begin
              gotoxy(45,5+a);
              writeln('MP');
              end;

              if (gg[a]<0) and (a>1) then
              begin
              gotoxy(45,5+a);
              writeln('AH');
              end;


  gotoxy(50,5+a);
  writeln('', h[a]:3:2);


              hh[a] := h[a]-h[a-1];

              if (hh[a]>0) and (a>1) then
              begin
              gotoxy(55,5+a);
              writeln('SH');
              end;

              if (hh[a]=0) and (a>1) then
              begin
              gotoxy(55,5+a);
              writeln('MP');
              end;

              if (hh[a]<0) and (a>1) then
              begin
              gotoxy(55,5+a);
              writeln('AH');
              end;}


 if (e[a]<0) then e[a]:=abs(e[a]);
{if (f[a]<0) then f[a]:=abs(f[a]);
 if (g[a]<0) then g[a]:=abs(g[a]);
 if (h[a]<0) then h[a]:=abs(h[a]);}


end;

writeln;

gotoxy(5,22);
writeln('   Aperte ENTER para continuar o programa');

readkey;


{###########################}




 {Calculo 1§ eixo A}



  Tempo   :=(1000/(RPM/3));
  Tempoi  :=(tempo);
  pulsos  :=e[a]*20;
  pulsoi  :=int(pulsos);
  tempoint:=trunc(tempoi);
  i:=1;

 while (i<pulsoi) do

 Begin

  if (ee[a]=0) and (a>1) then port[data]:=0;
  if (ee[a]>0) and (a>1) then port[data]:=1;{faz conversao pra binario}
  if (ee[a]<0) and (a>1) then port[data]:=3;{faz conversao pra binario}

  delay(tempoint);
  port[data]:=0;
  delay(tempoint);
  write('°');
  i:=i+1;
  resultadozero:=i mod 20;
  idivid20:=i/20;
 if resultadozero=0 then write('',idivid20:1:0,'');
 end;



 {Calculo 2§ eixo B}


 { Tempob:=(1000/(RPMb/3));
  Tempoib :=(tempob);
  pulsosb :=f[a]*20;
  pulsoib := int(pulsosb);
  tempointb := trunc(tempoib);
  ib:=1;

 while (ib<pulsoib) do

 Begin

  if (ff[a]>0)  then port[data]:=4;{faz conversao pra binario}
  {if (ff[a]<0)  then port[data]:=12;{faz conversao pra binario}


 { delay(tempointb);

  port[data]:=0;

  delay(tempointb);

  write('±');
  ib:=Ib+1;
  resultadozerob:=ib mod 20;
  idivid20b:=ib/20;

 if resultadozerob=0 then write('',idivid20b:1:0,'');
 end;


 {Calculo 3§ eixo C}


  {Tempoc:=(1000/(RPMc/3));
  Tempoic :=(tempoc);
  pulsosc :=g[a]*20;
  pulsoic := int(pulsosc);
  tempointc := trunc(tempoic);
  ic:=1;

 while (ic<pulsoic) do

 Begin


  if (gg[a]>0)  then port[data]:=16;{faz conversao pra binario}
 { if (gg[a]<0)  then port[data]:=48;{faz conversao pra binario}

  {delay(tempointc);

  port[data]:=0;

  delay(tempointc);

  write('²');
  ic:=Ic+1;
  resultadozeroc:=ic mod 20;
  idivid20c:=ic/20;

 if resultadozeroc=0 then write('',idivid20c:1:0,'');
 end;


 {Calculo 4§ eixo D}


 { Tempod:=(1000/(RPMd/3));
  Tempoid :=(tempod);
  pulsosd :=h[a]*20;
  pulsoid := int(pulsosd);
  tempointd := trunc(tempoid);
  id:=1;

while (id<pulsoid) do

 Begin


  if (hh[a]>0) then port[data]:=64;{faz conversao pra binario}
 { if (hh[a]<0) then port[data]:=192;{faz conversao pra binario}


  {delay(tempointd);

  port[data]:=0;

  delay(tempointd);

  write('#');
  id:=Id+1;
  resultadozerod:=id mod 20;
  idivid20d:=id/20;

 if resultadozerod=0 then write('',idivid20d:1:0,'');
 end;}

  writeln('');writeln('');writeln('');

  Writeln('                         A peca esta pronta!!!');

  writeln('                  Aperte qualquer tecla para encerrar');

  readkey;




end.