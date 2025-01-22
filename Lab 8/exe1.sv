//-------------------------------------Sudoku-------------------------------------//
class sudoku #(parameter N = 9);
    localparam int COLS = N;
    localparam int ROWS = N;
    localparam int COLS_BLOCK = (N % 2 == 0) ? N / 2: N / 3;
    localparam int ROWS_BLOCK = N / COLS_BLOCK;

    int unsigned puzzel[ROWS][COLS];
    rand int unsigned tmp[ROWS][COLS];
    
    // Constructor
    function new(input int unsigned puzzel[ROWS][COLS]);
      	this.puzzel = puzzel;
    endfunction

    // Constraint for puzzle values
  	constraint value{
      foreach(tmp[ROWS, COLS]){
        	// Random value range
        	tmp[ROWS][COLS] inside {[1:N]};
        
        	// Get the value from puzzel
        	puzzel[ROWS][COLS] != 0 -> tmp[ROWS][COLS] == puzzel[ROWS][COLS];
        }
    }  
     
     // Constraint for the row
    constraint row_cons{
        foreach(tmp[ROWS_OUT, COLS_OUT]){
            foreach(tmp[ROWS_IN, COLS_IN]){
                COLS_OUT != COLS_IN && ROWS_OUT == ROWS_IN -> tmp[ROWS_OUT][COLS_OUT] != tmp[ROWS_IN][COLS_IN];
            }
        }
     }
          
    // Constraint for the col
    constraint col_cons{
        foreach(tmp[ROWS_OUT, COLS_OUT]){
            foreach(tmp[ROWS_IN, COLS_IN]){
                COLS_OUT == COLS_IN && ROWS_OUT != ROWS_IN -> tmp[ROWS_OUT][COLS_OUT] != tmp[ROWS_IN][COLS_IN];
            }
        }
    }

    // Constraint for block
    constraint block_cons {
        foreach (tmp[ROWS_OUT, COLS_OUT]) {
            foreach (tmp[ROWS_IN, COLS_IN]) {
                if ((ROWS_OUT / ROWS_BLOCK == ROWS_IN / ROWS_BLOCK) && (COLS_OUT / COLS_BLOCK == COLS_IN / COLS_BLOCK)) {
                    if (!(ROWS_OUT == ROWS_IN && COLS_OUT == COLS_IN)) {
                        tmp[ROWS_OUT][COLS_OUT] != tmp[ROWS_IN][COLS_IN];
                    }
                }
            }
        }
    }


    // Display the result 
    function void display();
        foreach (tmp[ROWS]) begin
            foreach (tmp[ROWS][COLS]) begin
                $write("%0d ", tmp[ROWS][COLS]);
                if ((COLS + 1) % COLS_BLOCK == 0 && COLS != N - 1) 
                    $write("| ");
            end
            $write("\n");
            if ((ROWS + 1) % ROWS_BLOCK == 0 && ROWS != N - 1) begin
              	for (int i = 0; i < N-1; i++) begin
                  	$write("---");
                end
                $write("\n");
            end
        end
    endfunction

endclass

module sudoku_tb;
    sudoku #(4) sd_4size;
    int unsigned arr_4size[4][4] = '{
        '{0, 0, 0, 3},
        '{0, 0, 0, 1},
        '{1, 0, 0, 0},
        '{2, 0, 0, 0}
    };

  	sudoku #(6) sd_6size;
  	int unsigned arr_6size[6][6] = '{
        '{0, 4, 0, 0, 0, 0},
        '{0, 5, 6, 0, 0, 0},
        '{5, 0, 0, 3, 2, 0},
        '{0, 2, 3, 0, 0, 5},
        '{0, 0, 0, 5, 1, 0},
        '{0, 0, 0, 0, 6, 0}
    };

    sudoku #(9) sd_9size;
    int unsigned arr_9size[9][9] = '{
        '{0, 9, 8, 0, 0, 3, 7, 0, 6},
        '{0, 0, 2, 0, 0, 0, 0, 8, 0},
        '{0, 0, 0, 0, 0, 4, 1, 0, 9},
        '{0, 0, 6, 0, 0, 0, 0, 0, 0},
        '{0, 7, 0, 5, 0, 9, 0, 0, 0},
        '{0, 0, 0, 0, 7, 0, 0, 0, 8},
        '{1, 6, 0, 0, 0, 0, 5, 0, 0},
        '{0, 0, 0, 0, 4, 0, 0, 0, 0},
        '{0, 0, 3, 0, 2, 7, 0, 0, 0}
    };

    initial begin
        $display("-----------------Sudoku 4x4-----------------");
        sd_4size = new(arr_4size);
        assert(sd_4size.randomize());
        sd_4size.display();

        $display("-----------------Sudoku 6x6-----------------");
        sd_6size = new(arr_6size);
        assert(sd_6size.randomize());
        sd_6size.display();

        $display("-----------------Sudoku 9x9-----------------");
        sd_9size = new(arr_9size);
        assert(sd_9size.randomize());
        sd_9size.display();
    end
endmodule
