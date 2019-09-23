@echo off

del 1 2
lzmaSh2.exe geo_lzma 1
lzmaSh2a.exe geo_lzma 2
fc /b 1 2

