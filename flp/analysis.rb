#!/usr/bin/env ruby

require 'fileutils'
require 'open3'

TMP = 'tmp'
ROOT = FileUtils.pwd

def results(output)
  folds = {}
  list_folds = 0
  data_folds = 0

  output.lines.each do |line|
    words = line.split
    if words[0] == 'RewriteResult:' and words.last != 'NoFold' then
      name = words[1]
      unless folds[name]  # ensure we only count each fold once
        if words.last == 'ListFold' then
          list_folds += 1
        elsif words.last == 'DataFold' then
          data_folds += 1
        end
      end
    end
  end

  puts "ListFold: #{list_folds}"
  puts "DataFold: #{data_folds}"
end

def compile(name)
  print "Compiling #{name}: "
  cmd = 'ghc --make -package what-morphism -fplugin=WhatMorphism Main.hs 2>&1'

  cmd_start = Time.now
  output = `#{cmd}`
  status = $?
  cmd_end = Time.now

  elapsed = (cmd_end - cmd_start).floor
  if status.success? then
    print "success (#{elapsed}s)\n"
    results(output)
  else
    print "exit code #{status.exitstatus} (#{elapsed}s)\n"
  end
end

# Preventive cleanup
FileUtils.rm_rf TMP

zip_files = Dir.glob('*.zip').sort
zip_files.each do |zip_file|
  # Move over zip file
  FileUtils.mkdir TMP
  FileUtils.cp zip_file, TMP

  # Go to tmp dir and unzip
  FileUtils.cd TMP
  `unzip "#{zip_file}"`

  # Analysis
  compile(zip_file)

  # Remove tmp dir
  FileUtils.cd ROOT
  FileUtils.rm_r TMP
end
