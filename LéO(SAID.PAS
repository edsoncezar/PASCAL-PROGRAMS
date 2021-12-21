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

 if (sentido ='h') or (sentido='H') then port[data]:=1
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

 if (sentido ='h') or (sentido='H') then port[data]:=4
 else if (sentido='a') or (sentido='A')then port[data]:=12;

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

 if (sentido ='h') or (sentido='H') then port[data]:=16
 else if (sentido='a') or (sentido='A')then port[data]:=48;

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

 if (sentido ='h') or (sentido='H') then port[data]:=64
 else if (sentido='a') or (sentido='A')then port[data]:=192;

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