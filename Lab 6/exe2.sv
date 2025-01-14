//---------------------------------------------------Exercise 2---------------------------------------------------//
module exe2;
  event ev_1, ev_2;
  int var1, var2;

  initial begin
      fork
          begin
              #10;
              var1 = $urandom;
              -> ev_1;
          end
          begin
              #20;
              var2 = $urandom;
              -> ev_2;
          end
      join
  end

  initial begin
      #5;
      -> ev_1;
      @ (ev_1);
      $display("Time: %0t, ev_1 triggered, var1: %0d", $time, var1);
  end

  initial begin
      #15;
      -> ev_2;
      wait (ev_2.triggered);
      $display("Time: %0t, ev_2 triggered, var2: %0d", $time, var2);
  end
endmodule
