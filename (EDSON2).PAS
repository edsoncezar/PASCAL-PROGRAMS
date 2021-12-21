program saida;
uses crt;
var
  sentido:char;
bit1,bit2,bit3,bit4,bit5,bit6,bit7,bit8:byte;
d:real;
i,tempoint:integer;
RPM,RPMa,mm,pulsoi,tempoi,tempo,pulsos,k,z,resultadozero,voltasmin, idivid20:real;

iy,tempointy:integer;
RPMy,RPMay,mmy,pulsoiy,tempoiy,tempoy,pulsosy,ky,zy
,resultadozeroy,voltasminy, idivid20y:real;

iz,tempointz:integer;
RPMz,RPMaz,mmz,pulsoiz,tempoiz,tempoz,pulsosz,kz,zz
,resultadozeroz,voltasminz, idivid20z: real;
const
data=$378;
{status= data+1;
control=data+2}
begin
textcolor(14);
textbackground(1);
CLRSCR;
textcolor(44);
GOTOXY (20,6);Write('  ÉÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍ»  ');
GOTOXY (20,7);write('  º                                           º  ');
GOTOXY (20,8);write('  º            APERTE QUALQUER                º  ');
GOTOXY (20,9);write('  º                                           º  ');
GOTOXY (20,10);write('  º                 TECLA                     º  ');
GOTOXY (20,11);write('  º                                           º  ');
textcolor(34);
GOTOXY (20,12);write('  º              PARA INICIAR                 º  ');
GOTOXY (20,13);write('  º                                           º  ');
GOTOXY (20,14);write('  º              SEU PROGRAMA                 º  ');
GOTOXY (20,15);write('  º                                           º  ');
GOTOXY (20,16);write('  º                                           º  ');
GOTOXY (20,17);write('  ÈÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍ¼  ');
READKEY;
begin
clrscr;
sound(500);
delay(750);
SOUND(1750);
DELAY(750);
SOUND(2500);
DELAY(750);
nosound;
begin
 ClrScr;
textcolor(14);
textbackground(1);
clrscr;
writeln('');writeln('');writeln('');writeln('');
repeat
textcolor(13);

gotoxy(1,1);write('ÚÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄ¿  ÚÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄ¿');
gotoxy(1,2);write('³ quantos milimetros deseja andar em x===>       ³  ³                ³');
gotoxy(1,3);write('ÀÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÙ  ÀÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÙ');

gotoxy(60,2);readln(mm);
until (mm<=500);
repeat
textcolor(14);
gotoxy(1,5);write('ÚÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄ¿  ÚÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄ¿');
gotoxy(1,6);write('³ Qual a rota‡Æo do motor em RPM(RPM max=900)===>³  ³                 ³');
gotoxy(1,7);write('ÀÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÙ  ÀÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÙ');


gotoxy(60,6);readln(RPMa);
RPM:=RPMa*1;
until(RPM<=900);
repeat
textcolor(15);
gotoxy(1,9);write('ÚÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄ¿  ÚÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄ¿');
gotoxy(1,10);write('³ Sentido de rota‡Æo:H(hor rio) A (anti-hor rio)>³  ³                 ³');
gotoxy(1,11);write('ÀÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÙ  ÀÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÙ');

gotoxy(60,10);readln(sentido);
until(sentido='A')or (sentido='H') or (sentido='a') or (sentido='h');
tempo:=(1000/(RPM/3));
tempoi:=int(tempo);
pulsos:=mm*20;
pulsoi:=int(pulsos);
tempoint:=trunc(tempoi);
i:=1;
while (i<pulsoi) do
begin


if ( sentido='h') or ( sentido='H') then port[data] {bit1}:=2{8 164}
else if (sentido='a') or (sentido='A') then port[data]{bit1}:={7}3{255{48}{12};
delay (tempoint);

port[data]:={bit1}0;
{bit1:=0;}
delay(tempoint);

write('ÛşÛ');
i:=i+1;
resultadozero:=i mod 20;idivid20:=i/20;
if resultadozero=0 then write ('',idivid20:1:0,'');
end;

begin
textcolor(14);
textbackground(1);
clrscr;
writeln('');writeln('');writeln('');writeln('');
repeat
textcolor(13);
gotoxy(1,1);write('ÚÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄ¿  ÚÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄ¿');
gotoxy(1,2);write('³ quantos milimetros deseja andar em y===>       ³  ³                ³');
gotoxy(1,3);write('ÀÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÙ  ÀÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÙ');

gotoxy(60,2);readln(mmy);
until (mmy<=500);
repeat
textcolor(14);

gotoxy(1,5);write('ÚÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄ¿  ÚÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄ¿');
gotoxy(1,6);write('³ Qual a rota‡Æo do motor em RPMy(RPMy max=900)=>³  ³                ³');
gotoxy(1,7);write('ÀÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÙ  ÀÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÙ');

gotoxy(60,6);readln(RPMay);
RPMy:=RPMay*1;
until(RPMy<=900);
repeat
textcolor(15);
gotoxy(1,9);write('ÚÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄ¿  ÚÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄ¿');
gotoxy(1,10);write('³Sentido de rota‡Æo:H(hor rio) A (anti-hor rio)=>³  ³                ³');
gotoxy(1,11);write('ÀÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÙ  ÀÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÙ');


gotoxy(60,10);readln(sentido);
until(sentido='A')or (sentido='H') or (sentido='a') or (sentido='h');
tempoy:=(1000/(RPMy/3));
tempoiy:=int(tempoy);
pulsosy:=mmy*20;
pulsoiy:=int(pulsosy);
tempointy:=trunc(tempoiy);
iy:=1;
while (iy<pulsoiy) do
begin
if ( sentido='h') or ( sentido='H') then port[data] {bit1}:=2{8 164}
else if (sentido='a') or (sentido='A') then port[data]{bit1}:={7}3{255{48}{12};
delay (tempointy);

port[data]:={bit1}0;
{bit1:=0;}
delay(tempointy);

write('ÛßÛ');
iy:=iy+1;
resultadozeroy:=iy mod 20;
idivid20y:=iy/20;
if resultadozeroy=0 then write ('',idivid20y:1:0,'');
end;

begin
textcolor(14);
textbackground(1);
clrscr;
writeln('');writeln('');writeln('');writeln('');
repeat
textcolor(13);
gotoxy(1,1);write('ÚÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄ¿  ÚÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄ¿');
gotoxy(1,2);write('³Quantos milimetros deseja andar em z    ====>   ³  ³                ³');
gotoxy(1,3);write('ÀÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÙ  ÀÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÙ');


gotoxy(60,2);readln(mmz);
until (mmz<=500);
repeat
textcolor(14);
gotoxy(1,5);write('ÚÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄ¿  ÚÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄ¿');
gotoxy(1,6);write('³Qual a rota‡Æo do motor em RPMz(RPMz max=900)==>³  ³                ³');
gotoxy(1,7);write('ÀÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÙ  ÀÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÙ');

gotoxy(60,6);readln(RPMaz);
RPMz:=RPMaz*1;
until(RPMz<=900);
repeat
textcolor(15);
gotoxy(1,9);write('ÚÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄ¿  ÚÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄ¿');
gotoxy(1,10);write('³Sentido de rota‡Æo:H(hor rio) A (anti-hor rio)=>³  ³                ³');
gotoxy(1,11);write('ÀÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÙ  ÀÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÙ');

gotoxy(60,10);readln(sentido);
until(sentido='A')or (sentido='H') or (sentido='a') or (sentido='h');
tempoz:=(1000/(RPMz/3));
tempoiz:=int(tempoz);
pulsosz:=mmz*20;
pulsoiz:=int(pulsosz);
tempointz:=trunc(tempoiz);
iz:=1;
while (iz<pulsoiz) do

begin
if ( sentido='h') or ( sentido='H') then port[data] {bit1}:=2{8 164}
else if (sentido='a') or (sentido='A') then port[data]{bit1}:={7}3{255{48}{12};
delay (tempointz);

port[data]:={bit1}0;
{bit1:=0;}
delay(tempointz);

write('ÛÜÛ');
iz:=iz+1;
resultadozeroz:=iz mod 20;
idivid20z:=iz/20;
if resultadozeroz=0 then write ('',idivid20z:1:0,'');
end;
{port[data]:=bit3;
bit3:=0;}
DELAY(750);

begin
Textcolor(250);
textbackground(1);
clrscr;
sound(500);
delay(750);
SOUND(1000);
DELAY(750);
SOUND(1500);
DELAY(750);
Nosound;
writeln('');writeln('');writeln('');writeln('');

CLRSCR;
GOTOXY (20,6);Write('  ÉÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍ»  ');
GOTOXY (20,7);write('  º                                           º  ');
GOTOXY (20,8);write('  º            APERTE QUALQUER                º  ');
GOTOXY (20,9);write('  º                                           º  ');
GOTOXY (20,10);write('  º                 TECLA                     º  ');
GOTOXY (20,11);write('  º                                           º  ');
GOTOXY (20,12);write('  º            PARA FINALIZAR                 º  ');
GOTOXY (20,13);write('  º                                           º  ');
GOTOXY (20,14);write('  º             SEU PROGRAMA                  º  ');
GOTOXY (20,15);write('  º                                           º  ');
GOTOXY (20,16);write('  º                                           º  ');
GOTOXY (20,17);write('  ÈÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍ¼  ');

READKEY;
end;
end;
END;
end;
end;
END.



