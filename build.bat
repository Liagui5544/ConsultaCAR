@echo off
echo === Consulta CAR - Build ===
echo.

pyinstaller --onedir --windowed ^
  --name "Consulta CAR" ^
  --icon car.ico ^
  --add-data "car.ico;." ^
  --collect-all shapely ^
  --hidden-import shapely ^
  --hidden-import numpy ^
  --hidden-import PIL ^
  --hidden-import requests ^
  --hidden-import tkintermapview ^
  --add-data "lib/tkintermapview;tkintermapview" ^
  --noconfirm ^
  consulta_car_ui.py

echo.
echo Build concluido. Executavel em dist\Consulta CAR\
pause
