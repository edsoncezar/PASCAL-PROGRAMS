Program eixos;

Uses Crt;

Var

e,ee:array[1..100] of real;
f,ff:array[1..100] of real;
g,gg:array[1..100] of real;
h,hh:array[1..100] of real;


a,b:integer;
ch:char;

Begin

a:=0;
b:=0;

textcolor(14);
Clrscr;

Repeat

Clrscr;

a:=a+1;
b:=b+1;


writeln;

  gotoxy(1,5);
  write('  Entre com o valor da coordenada A====>        ');
  readln(e[a]);

  gotoxy(1,6);
  write('  Entre com o valor da coordenada B====>        ');
  readln(f[a]);

  gotoxy(1,7);
  write('  Entre com o valor da coordenada C====>        ');
  readln(g[a]);

  gotoxy(1,8);
  write('  Entre com o valor da coordenada D====>        ');
  readln(h[a]);


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


  gotoxy(30,5+a);
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
                                 {portdata := 2;    { <<<<<=======aqui abre
                                     porta de comunica‡Æo em bin rio}
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
              end;


 if (e[a]<0) then e[a]:=abs(e[a]);
 if (f[a]<0) then f[a]:=abs(f[a]);
 if (g[a]<0) then g[a]:=abs(g[a]);
 if (h[a]<0) then h[a]:=abs(h[a]);


end;

writeln;

gotoxy(5,22);
writeln('   Aperte ENTER para encerrar');

readln;

end.




{###########################}




program saida;

uses crt;

var

  sentido:char;
  bit1, bit2, bit3, bit4, bit5, bit6, bit7, bit8:byte;

  {eixo A}

  i, tempoint:integer;
  mm,pulsoi,tempoi,k,z,resultadozero,idivid20:real;
  pulsos,voltasmin,tempo,RPMa,rpm:real;

  {eixo B}

  iB, tempointB:integer;
  mmB,pulsoiB,tempoiB,kB,zB,resultadozeroB,idivid20B:real;
  pulsosB,voltasminB,tempoB,RPMaB,rpmB:real;

  {eixo C}

  iC, tempointC:integer;
  mmC,pulsoiC,tempoiC,kC,zC,resultadozeroC,idivid20C:real;
  pulsosC,voltasminC,tempoC,RPMaC,rpmC:real;

  {eixo D}

  iD, tempointD:integer;
  mmD,pulsoiD,tempoiD,kD,zD,resultadozeroD,idivid20D:real;
  pulsosD,voltasminD,tempoD,RPMaD,rpmD:real;

Const

  data=$378;

 {1§ eixo A}

 begin

  clrscr;
  writeln('');writeln('');writeln('');writeln('');

  write('quantos milimetros deseja andar ============================>');
  readln(mm);

  write('Qual a rota‡Æo do motor em RPM (RPM max = 900 ==============>');
  readln(RPMa);

  RPM :=RPMa*3.2;

  write('qual o sentido de rota‡Æo: H (hor rio) ou A (anti-hor rio)==>');
  Readln(sentido);

 {2§ eixo B}

 begin

  clrscr;
  writeln('');writeln('');writeln('');writeln('');

  write('quantos milimetros deseja andar ============================>');
  readln(mmb);

  write('Qual a rota‡Æo do motor em RPM (RPM max = 900 ==============>');
  readln(RPMab);

  RPMb :=RPMab*3.2;

  write('qual o sentido de rota‡Æo: H (hor rio) ou A (anti-hor rio)==>');
  Readln(sentido);

 end;

 {3§ eixo C}

 begin

  clrscr;
  writeln('');writeln('');writeln('');writeln('');

  write('quantos milimetros deseja andar ============================>');
  readln(mmc);

  write('Qual a rota‡Æo do motor em RPM (RPM max = 900 ==============>');
  readln(RPMac);

  RPMc :=RPMac*3.2;

  write('qual o sentido de rota‡Æo: H (hor rio) ou A (anti-hor rio)==>');
  Readln(sentido);

 end;

 {4§ eixo D}

 begin

  clrscr;
  writeln('');writeln('');writeln('');writeln('');

  write('quantos milimetros deseja andar ============================>');
  readln(mmd);

  write('Qual a rota‡Æo do motor em RPM (RPM max = 900 ==============>');
  readln(RPMad);

  RPMd :=RPMad*3.2;

  write('qual o sentido de rota‡Æo: H (hor rio) ou A (anti-hor rio)==>');
  Readln(sentido);

 end;


 {Calculo 1§ eixo A}



  Tempo:=(1000/(RPM/3));
  Tempoi :=(tempo);
  pulsos := mm*20;
  pulsoi := int(pulsos);
  tempoint := trunc(tempoi);
  i:=1;

 while (i<pulsoi) do

 Begin

 if (sentido ='h') or (sentido='H') then port[data]:=2
 else if (sentido='a') or (sentido='A')then port[data]:=3;

  delay(tempoint);

  port[data]:=0;

  delay(tempoint);

  write('°');
  i:=I+1;
  resultadozero:=i mod 20;
  idivid20:=i/20;

 if resultadozero=0 then write('',idivid20:1:0,'');
 end;


 {Calculo 2§ eixo B}


  Tempob:=(1000/(RPMb/3));
  Tempoib :=(tempob);
  pulsosb := mmb*20;
  pulsoib := int(pulsosb);
  tempointb := trunc(tempoib);
  ib:=1;

 while (ib<pulsoib) do

 Begin

 if (sentido ='h') or (sentido='H') then port[data]:=2
 else if (sentido='a') or (sentido='A')then port[data]:=3;

  delay(tempointb);

  port[data]:=0;

  delay(tempointb);

  write('±');
  ib:=Ib+1;
  resultadozerob:=ib mod 20;
  idivid20b:=ib/20;

 if resultadozerob=0 then write('',idivid20b:1:0,'');
 end;


 {Calculo 3§ eixo C}


  Tempoc:=(1000/(RPMc/3));
  Tempoic :=(tempoc);
  pulsosc := mmc*20;
  pulsoic := int(pulsosc);
  tempointc := trunc(tempoic);
  ic:=1;

 while (ic<pulsoic) do

 Begin

 if (sentido ='h') or (sentido='H') then port[data]:=2
 else if (sentido='a') or (sentido='A')then port[data]:=3;

  delay(tempointc);

  port[data]:=0;

  delay(tempointc);

  write('²');
  ic:=Ic+1;
  resultadozeroc:=ic mod 20;
  idivid20c:=ic/20;

 if resultadozeroc=0 then write('',idivid20c:1:0,'');
 end;


 {Calculo 4§ eixo D}


  Tempod:=(1000/(RPMd/3));
  Tempoid :=(tempod);
  pulsosd := mmd*20;
  pulsoid := int(pulsosd);
  tempointd := trunc(tempoid);
  id:=1;

while (id<pulsoid) do

 Begin

 if (sentido ='h') or (sentido='H') then port[data]:=2
 else if (sentido='a') or (sentido='A')then port[data]:=3;

  delay(tempointd);

  port[data]:=0;

  delay(tempointd);

  write('#');
  id:=Id+1;
  resultadozerod:=id mod 20;
  idivid20d:=id/20;

 if resultadozerod=0 then write('',idivid20d:1:0,'');
 end;

  writeln('');writeln('');writeln('');

  Writeln('                         A peca esta pronta!!!');

  writeln('                  Aperte qualquer tecla para encerrar');

  readkey;




end.