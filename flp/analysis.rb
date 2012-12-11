#!/usr/bin/env ruby

require 'fileutils'
require 'open3'
require 'tempfile'

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

def compile(command, name)
  print "Compiling #{name}: "

  start = Time.now
  output = `#{command}`
  status = $?

  elapsed = (Time.now - start).floor
  if status.success? then
    print "success (#{elapsed}s)\n"
    results(output)
  else
    print "exit code #{status.exitstatus} (#{elapsed}s)\n"
  end

  log = `mktemp /tmp/whatmorpism-XXXXX`.chomp
  File.open(log, 'w') { |f| f.write(output) }
  puts "Log written to #{log}"
end

def compile_zip(name)
  # Preventive cleanup
  FileUtils.rm_rf TMP

  # Move over zip file
  FileUtils.mkdir TMP
  FileUtils.cp name, TMP

  # Go to tmp dir and unzip
  FileUtils.cd TMP
  `unzip "#{name}"`

  # Analysis
  command = 'ghc --make -package what-morphism -fplugin=WhatMorphism Main.hs 2>&1'
  compile(command, name)

  # Remove tmp dir
  FileUtils.cd ROOT
  FileUtils.rm_r TMP
end

def compile_cabal(name)
  package = name.chomp('.tar.gz')
  `tar -xzf #{name}`

  FileUtils.cd package
  cabal_file = Dir.glob('*.cabal').first

  patched = File.read(cabal_file).gsub(/(library)(\s+)/i) do
    "#{$1}#{$2}" +
      "build-depends: what-morphism#{$2}" +
      "ghc-options: -fplugin=WhatMorphism#{$2}"
  end

  File.open(cabal_file, 'w') { |f| f.write(patched) }

  command = 'cabal configure && cabal build 2>&1'
  compile(command, package)

  FileUtils.cd ROOT
  FileUtils.rm_r package
end

file = ARGV[0]

if file.end_with? '.zip'
  compile_zip(file)
elsif file.end_with? '.tar.gz'
  compile_cabal(file)
end
